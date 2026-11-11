// SPDX-License-Identifier: AGPL-3.0-or-later
// Regression tests of the editor side of the protocol, run against the REAL functions of
// src/extension.ts (EXT_FILE overrides the file, to replay a test against an older version).
// Rule: a daemon message with revision == editor_rev must end in exactly one of
//   apply / no-op (daemon += 1)  or  reject (empty delta with revision = daemon, editor += 1);
// a message with another revision is ignored.
const assert = require("node:assert/strict")
const path = require("node:path")
const {Mutex} = require("async-mutex")
const {loadReal} = require("./real.cjs")

const file = process.env.EXT_FILE ?? path.join(__dirname, "../src/extension.ts")
const uri = "file:///note.txt"

function setup({applyEdit, convert = () => [], content = () => "new", withDocument = true, daemon = 0, editor = 0}) {
    const sent = [], errors = []
    const document = {version: 1, text: "base", getText() { return this.text }, save: async () => true}
    const client = {
        name: "c", directory: "/d",
        ot_states: {[uri]: {revision: {daemon, editor}, content: ["base"]}},
        connection: {sendRequest: (type, edit) => { sent.push(edit); return Promise.resolve() }},
    }
    const {context, fns} = loadReal(["processEditFromDaemon"], {
        mutex: new Mutex(), pendingRemote: null, editType: "edit", debug() {},
        documentForUri: () => (withDocument ? document : undefined),
        teamtypevDeltasToVSCodeTextEdits: convert, contentAfterEdits: content,
        applyEdit: applyEdit ?? (async () => true),
        processLocalEdit() {}, 
        vscode: {window: {showErrorMessage(m) { errors.push(String(m)) }}},
    }, file)
    return {client, sent, errors, run: edit => fns.processEditFromDaemon(client, edit)}
}
const rev = c => [c.ot_states[uri].revision.daemon, c.ot_states[uri].revision.editor]
const empties = sent => sent.filter(e => e.delta.length === 0).map(e => [e.revision])

async function main() {
    // ignore-stale: no state change, nothing sent
    for (const r of [0, 2]) {
        const t = setup({editor: 1, daemon: 1})
        await t.run({uri, revision: r, delta: []})
        assert.deepEqual(rev(t.client), [1, 1]); assert.equal(t.sent.length, 0)
    }
    // unchanged content counts as applied
    {
        const t = setup({content: () => "base"})
        await t.run({uri, revision: 0, delta: []})
        assert.deepEqual(rev(t.client), [1, 0]); assert.equal(t.sent.length, 0)
    }
    // reject: position conversion throws (daemon edit does not fit the buffer)
    {
        const t = setup({convert: () => { throw new Error("Could not convert char offset") }, daemon: 3, editor: 3})
        await t.run({uri, revision: 3, delta: [{}]})
        assert.deepEqual(rev(t.client), [3, 4]); assert.deepEqual(empties(t.sent), [[3]])
        assert.equal(t.errors.length, 1)
    }
    // reject: workspace.applyEdit throws
    {
        const t = setup({applyEdit: async () => { throw new Error("boom") }})
        await t.run({uri, revision: 0, delta: [{}]})
        assert.deepEqual(rev(t.client), [0, 1]); assert.deepEqual(empties(t.sent), [[0]])
    }
    // reject: applyEdit returns false (existing behaviour)
    {
        const t = setup({applyEdit: async () => false})
        await t.run({uri, revision: 0, delta: [{}]})
        assert.deepEqual(rev(t.client), [0, 1]); assert.deepEqual(empties(t.sent), [[0]])
    }
    // reject: state exists but no document
    {
        const t = setup({withDocument: false})
        await t.run({uri, revision: 0, delta: [{}]})
        assert.deepEqual(rev(t.client), [0, 1]); assert.deepEqual(empties(t.sent), [[0]])
    }
    // closed uri: no state, ignored without effect
    {
        const t = setup({})
        delete t.client.ot_states[uri]
        await t.run({uri, revision: 0, delta: [{}]})
        assert.equal(t.sent.length, 0)
    }

    // contentAfterEdits: two insertions at one point keep their order (VS Code applies them in order)
    {
        const {fns} = loadReal(["contentAfterEdits"], {})
        const d = {getText: () => "0123456789", offsetAt: p => p.o}
        const ed = (s, e, t) => ({range: {start: {o: s}, end: {o: e}}, newText: t})
        assert.equal(fns.contentAfterEdits(d, [ed(5, 5, "A"), ed(5, 5, "B")]), "01234AB56789")
        assert.equal(fns.contentAfterEdits(d, [ed(5, 5, "A"), ed(5, 6, "")]), "01234A6789")
        assert.equal(fns.contentAfterEdits(d, [ed(2, 3, "X"), ed(7, 7, "Y")]), "01X3456Y789")
    }

    // handoffDelta: applying the delta to `before` (daemon positions: LF-only lines, char columns) gives `after`
    {
        const {fns} = loadReal(["handoffDelta"], {})
        const atoms = ["a", "b", "\n", "\r\n", "\r", "🥕", " ", "é", "字", "\u0085"]
        let seed = 12345
        const rnd = n => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed % n }
        const gen = () => Array.from({length: rnd(7)}, () => atoms[rnd(atoms.length)]).join("")
        const off = (text, p) => {
            const lines = text.split("\n")
            assert.ok(p.line < lines.length)
            const chars = [...lines[p.line]]
            assert.ok(p.character <= chars.length)
            return [...lines.slice(0, p.line).join("\n")].length + (p.line ? 1 : 0) + p.character
        }
        for (let i = 0; i < 20000; i++) {
            const before = gen(), after = gen()
            const delta = fns.handoffDelta(before, after)
            if (!delta.length) { assert.equal(before, after); continue }
            assert.equal(delta.length, 1)
            const b = [...before]
            const s = off(before, delta[0].range.start), e = off(before, delta[0].range.end)
            assert.ok(s <= e)
            assert.equal(b.slice(0, s).join("") + delta[0].replacement + b.slice(e).join(""), after)
        }
    }

    // close then reopen: an old-session message with revision == new editor revision must not be applied
    {
        const sent = []
        let answerClose
        const closeAnswer = new Promise(r => { answerClose = r })
        const client = {
            name: "c", directory: "/d", ot_states: {[uri]: {revision: {daemon: 0, editor: 0}, content: []}},
            connection: {sendRequest: (type, p) => (type === "close" ? closeAnswer : Promise.resolve(sent.push(p)))},
        }
        const mutex = new Mutex()
        const document = {uri: {scheme: "teamtypev"}, version: 1, getText: () => "base", save: async () => true}
        const {fns} = loadReal(["processEditFromDaemon", "processUserClose", "waitForClosedSession", "closingKey", "closingDocuments"], {
            mutex, pendingRemote: null, editType: "edit", closeType: "close", debug() {},
            documentForUri: () => document, protocolUri: () => uri, clientsForDocument: () => [client],
            teamtypevDeltasToVSCodeTextEdits: () => [], contentAfterEdits: () => "OLD-SESSION-EDIT",
            applyEdit: async () => { client.applied = (client.applied ?? 0) + 1; return false },
            processLocalEdit() {}, vscode: {window: {showErrorMessage() {}}},
        }, file)
        const release = await mutex.acquire() // the mutex is busy, so the old message queues
        const old = fns.processEditFromDaemon(client, {uri, revision: 0, delta: [{}]})
        fns.processUserClose(document)
        assert.equal(client.ot_states[uri], undefined)
        let reopened = false
        const reopen = fns.waitForClosedSession(client, uri).then(() => {
            client.ot_states[uri] = {revision: {daemon: 0, editor: 0}, content: []} // what openSharedDocument does next
            reopened = true
        })
        await new Promise(r => setTimeout(r, 10))
        assert.equal(reopened, false, "reopen must wait for the daemon's answer to close")
        answerClose("ok")
        release()
        await Promise.all([old, reopen])
        assert.equal(client.applied ?? 0, 0, "old-session message was applied to the reopened session")
        assert.deepEqual(rev(client), [0, 0])
    }
    {
        const {fns} = loadReal(["hasLoneCarriageReturn"], {})
        assert.equal(fns.hasLoneCarriageReturn("a\rb"), true)
        assert.equal(fns.hasLoneCarriageReturn("a\r"), true)
        assert.equal(fns.hasLoneCarriageReturn("a\r\nb\n"), false)
        assert.equal(fns.hasLoneCarriageReturn("a\u2028b\u0085"), false)
    }
    console.log("protocol regressions passed")
}
main().catch(e => { console.error(e); process.exitCode = 1 })
