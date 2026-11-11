// SPDX-License-Identifier: AGPL-3.0-or-later
// Randomized protocol scenarios against a reference state machine, run against the REAL functions of
// src/extension.ts (EXT_FILE overrides the file). Mirrors nvim-plugin/test/run.lua section 6 and the
// Emacs test teamtypev-random-protocol-scenarios. Events in random order: local edit, daemon edit
// (revision in {editor, editor-1, editor+1, 0}; fitting or not), close, reopen, answer to the current
// or a stale open request (success or failure).
// VS Code starts a session when it sends `open` (the daemon reads `open` before any later edit), so
// the oracle's session is live from the open request until close or a failed answer to its own open.
// Rules: a daemon message is applied iff live and revision == editor (daemon += 1); if it cannot be
// applied, an empty delta with revision = daemon is sent and editor += 1; otherwise ignored. Local
// edits are sent with revision = daemon, then editor += 1.
const assert = require("node:assert/strict")
const path = require("node:path")
const {Mutex} = require("async-mutex")
const {loadReal} = require("./real.cjs")

const file = process.env.EXT_FILE ?? path.join(__dirname, "../src/extension.ts")
const uri = "file:///note.txt"
const flush = async () => {
    for (let i = 0; i < 5; i++) await new Promise((r) => setImmediate(r))
}

class Position {
    constructor(line, character) {
        this.line = line
        this.character = character
    }
}
class Range {
    constructor(start, end) {
        this.start = start
        this.end = end
    }
}
class TextEdit {
    constructor(range, newText) {
        this.range = range
        this.newText = newText
    }
    static replace(range, newText) {
        return new TextEdit(range, newText)
    }
}

function makeDocument(text) {
    const doc = {
        uri: {scheme: "teamtypev"},
        version: 1,
        text,
        getText() {
            return this.text
        },
        get lineCount() {
            return this.text.split("\n").length
        },
        lineAt(n) {
            const lines = this.text.split("\n")
            if (n < 0 || n >= lines.length) throw new Error(`Illegal value for line ${n}`)
            return {text: lines[n]}
        },
        offsetAt(p) {
            return (
                this.text
                    .split("\n")
                    .slice(0, p.line)
                    .reduce((a, l) => a + l.length + 1, 0) + p.character
            )
        },
        save: async () => true,
    }
    return doc
}

async function scenario(seed) {
    let s = seed
    const rnd = (n) => {
        // mulberry32
        s = (s + 0x6d2b79f5) | 0
        let t = Math.imul(s ^ (s >>> 15), 1 | s)
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
        return ((t ^ (t >>> 14)) >>> 0) % n
    }
    const sent = []
    const opens = [] // pending open requests: {resolve, reject, token}
    const document = makeDocument("abc\ndef\n")
    const client = {
        name: "c",
        directory: "/d",
        ot_states: {},
        connection: {
            sendRequest(type, p) {
                const method = typeof type === "string" ? type : type.method
                if (method === "edit") {
                    sent.push(p)
                    return Promise.resolve("ok")
                }
                if (method === "close") return Promise.resolve("ok")
                if (method === "open") {
                    let o
                    const promise = new Promise((resolve, reject) => {
                        o = {resolve, reject}
                    })
                    promise.catch(() => {})
                    opens.push(o)
                    return promise
                }
                return Promise.resolve()
            },
        },
    }
    const globals = {
        mutex: new Mutex(),
        pendingRemote: null,
        editType: {method: "edit"},
        closeType: {method: "close"},
        Revision: class {
            daemon = 0
            editor = 0
        },
        debug() {},
        closingDocuments: new Map(),
        documentForUri: () => document,
        protocolUri: () => uri,
        getLines: (d) => d.getText().split("\n"),
        vscode: {Position, Range, TextEdit, window: {showErrorMessage() {}}},
    }
    const names = [
        "processEditFromDaemon",
        "processUserClose",
        "waitForClosedSession",
        "closingKey",
        "startSharedSession",
        "handoffDelta",
        "processUserEdit",
        "processLocalEdit",
        "rememberNativeChange",
        "clientsForDocument",
        "clientTracksDocument",
        "vsCodeChangeEventToTeamtypevEdits",
        "vsCodeChangeToTeamtypevDelta",
        "vsCodeRangeToTeamtypevRange",
        "vsCodePositionToTeamtypevPosition",
        "UTF16CodeUnitOffsetToCharOffset",
        "teamtypevDeltasToVSCodeTextEdits",
        "teamtypevRangeToVSCodeRange",
        "teamtypevPositionToVSCodePosition",
        "charOffsetToUTF16CodeUnitOffset",
        "contentAfterEdits",
    ]
    const {context, fns} = loadReal(names, globals, file)
    context.clients = [client]
    context.nativeCleanContents = new WeakMap()
    context.pendingNativeCleanContents = new WeakMap()
    // The editor buffer: an edit changes the text and fires onDidChangeTextDocument (processUserEdit).
    const change = (range, text) => {
        const a = document.offsetAt(range.start),
            b = document.offsetAt(range.end)
        document.text = document.text.slice(0, a) + text + document.text.slice(b)
        document.version += 1
        fns.processUserEdit({document, contentChanges: [{range, text}]})
    }
    context.applyEdit = async (c, d, edit) => {
        const [e] = fns.teamtypevDeltasToVSCodeTextEdits(d, edit.delta)
        change(e.range, e.newText)
        return true
    }

    let o = {live: false, dr: 0, er: 0}
    let current = null // the open request of the current session
    const reopen = async () => {
        const handoff = rnd(4) === 0
        const before = sent.length
        const started = fns.startSharedSession(
            client,
            uri,
            document.getText().split("\n"),
            document.getText(),
            handoff ? "H" + document.getText() : document.getText(),
            async () => {},
        )
        started.catch(() => {})
        await flush()
        current = opens[opens.length - 1]
        o = {live: true, dr: 0, er: handoff ? 1 : 0}
        if (handoff) {
            assert.equal(sent.length, before + 1)
            assert.deepEqual([sent.at(-1).revision, sent.at(-1).delta.length], [0, 1])
        }
    }
    await reopen()
    for (let step = 0; step < 40; step++) {
        const kind = rnd(7)
        const ctx = `seed ${seed} step ${step} kind ${kind}`
        if (kind === 0) {
            // answer to the current or a stale open, each answered once
            const pending = opens.filter((x) => !x.answered)
            if (!pending.length) continue
            const req = pending[rnd(pending.length)]
            req.answered = true
            const ok = rnd(2) === 0
            if (ok) req.resolve("ok")
            else req.reject(new Error("open failed"))
            await flush()
            if (req === current && !ok) o.live = false
        } else if (kind === 1) {
            if (o.live || client.ot_states[uri]) fns.processUserClose(document)
            o.live = false
            await flush()
        } else if (kind === 2) {
            if (!o.live) await reopen()
        } else if (kind === 3) {
            // local edit
            const n = sent.length
            change(new Range(new Position(0, 0), new Position(0, 0)), "x")
            if (o.live) {
                assert.equal(sent.length, n + 1, ctx + " local edit sent")
                assert.deepEqual([sent.at(-1).revision, sent.at(-1).delta.length], [o.dr, 1], ctx)
                o.er += 1
            } else assert.equal(sent.length, n, ctx + " local edit outside a session must not be sent")
        } else {
            // daemon edit
            const revs = [o.er, o.er, o.er - 1, o.er + 1, 0]
            const rev = revs[rnd(revs.length)]
            const fits = rnd(3) > 0
            const p = fits ? {line: 0, character: 0} : {line: 40, character: 0}
            const before = document.getText(),
                n = sent.length
            await fns.processEditFromDaemon(client, {
                uri,
                revision: rev,
                delta: [{range: {start: p, end: p}, replacement: "D"}],
            })
            if (o.live && rev === o.er) {
                if (fits) {
                    assert.equal(document.getText(), "D" + before, ctx + " daemon edit applied")
                    assert.equal(sent.length, n, ctx + " applied edit sends nothing")
                    o.dr += 1
                } else {
                    assert.equal(document.getText(), before, ctx + " rejected edit changes nothing")
                    assert.equal(sent.length, n + 1, ctx + " rejection sends an empty delta")
                    assert.deepEqual([sent.at(-1).revision, sent.at(-1).delta.length], [o.dr, 0], ctx)
                    o.er += 1
                }
            } else {
                assert.equal(document.getText(), before, ctx + " stale or sessionless edit ignored")
                assert.equal(sent.length, n, ctx + " stale or sessionless edit sends nothing")
            }
        }
        const st = client.ot_states[uri]
        if (o.live) assert.deepEqual(st && [st.revision.daemon, st.revision.editor], [o.dr, o.er], ctx + " revisions")
        else assert.equal(st, undefined, ctx + " no session state")
    }
}

async function main() {
    for (let seed = 1; seed <= 300; seed++) await scenario(seed)
    console.log("randomized protocol scenarios passed")
}
main().catch((e) => {
    console.error(e)
    process.exitCode = 1
})
