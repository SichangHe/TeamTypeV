// SPDX-License-Identifier: AGPL-3.0-or-later
// Randomized protocol scenarios against a reference state machine of the rules proved in
// editor_proof (editor rejection, many sessions over time), run against the REAL
// processEditFromDaemon of src/extension.ts (EXT_FILE overrides the file).
// Events in random order: daemon edits with revision in {editor, editor, editor-1, editor+1, 0}
// that fit or not (position conversion throws, or applyEdit fails or returns false), close, reopen.
// Oracle: a daemon edit is applied iff a session exists and revision == editor; then daemon += 1.
// A rejected one sends an empty delta with revision = daemon and counts editor += 1; others are ignored.
const assert = require("node:assert/strict")
const path = require("node:path")
const {Mutex} = require("async-mutex")
const {loadReal} = require("./real.cjs")

const file = process.env.EXT_FILE ?? path.join(__dirname, "../src/extension.ts")
const uri = "file:///note.txt"

async function scenario(seed) {
    let s = (seed * 2654435761) % 4294967296
    const rnd = (n) => ((s = (s * 1103515245 + 12345) & 0x7fffffff), s % n)
    const sent = []
    const document = {
        version: 1,
        text: "base",
        getText() {
            return this.text
        },
        save: async () => true,
    }
    let mode = "fit"
    const client = {
        name: "c",
        directory: "/d",
        ot_states: {},
        connection: {
            sendRequest: (type, edit) => {
                sent.push(edit)
                return Promise.resolve()
            },
        },
    }
    const open = () => {
        client.ot_states[uri] = {revision: {daemon: 0, editor: 0}, content: ["base"]}
    }
    let ctx
    const {fns, context} = loadReal(
        ["processEditFromDaemon"],
        {
            mutex: new Mutex(),
            pendingRemote: null,
            editType: "edit",
            debug() {},
            documentForUri: () => document,
            teamtypevDeltasToVSCodeTextEdits: () => {
                if (mode === "convert") throw new Error("does not fit")
                return []
            },
            contentAfterEdits: () => "changed",
            applyEdit: async () => {
                if (mode === "throw") throw new Error("boom")
                if (mode === "false") return false
                // the edit lands: VS Code reports the change event while pendingRemote is set
                const pr = context.pendingRemote
                pr.changes.push({event: {}, lines: ["changed"], content: pr.content, version: pr.version + 1})
                return true
            },
            processLocalEdit() {},
            vscode: {window: {showErrorMessage() {}}},
        },
        file,
    )
    let live = false,
        dr = 0,
        er = 0
    for (let step = 0; step < 40; step++) {
        const kind = rnd(5),
            ctx = `seed ${seed} step ${step} kind ${kind}`
        if (kind === 0) {
            delete client.ot_states[uri]
            live = false
        } else if (kind === 1) {
            open()
            live = true
            dr = er = 0
        } else {
            const revs = [er, er, er - 1, er + 1, 0]
            const rev = revs[rnd(revs.length)]
            mode = ["fit", "convert", "throw", "false"][rnd(4)]
            const before = sent.length
            // the "fit" mode lands through the pendingRemote path of the real code, which our mock
            // applyEdit does not drive: it reports the remote change itself below.
            const p = fns.processEditFromDaemon(client, {uri, revision: rev, delta: [{}]})
            await p
            if (live && rev === er) {
                if (mode === "fit") {
                    assert.equal(sent.length, before, ctx + " applied edit must not be answered")
                    dr += 1
                } else {
                    assert.equal(sent.length, before + 1, ctx)
                    assert.equal(
                        JSON.stringify(sent[sent.length - 1]),
                        JSON.stringify({uri, revision: dr, delta: []}),
                        ctx + ` mode ${mode}`,
                    )
                    er += 1
                }
            } else {
                assert.equal(sent.length, before, ctx + " stale or sessionless edit must be ignored")
            }
        }
        if (live) {
            const r = client.ot_states[uri].revision
            assert.deepEqual([r.daemon, r.editor], [dr, er], `seed ${seed} step ${step} revisions`)
        } else {
            assert.equal(client.ot_states[uri], undefined)
        }
    }
}

async function main() {
    for (let seed = 1; seed <= 300; seed++) await scenario(seed)
    console.log("random protocol scenarios passed")
}
main().catch((e) => {
    console.error(e)
    process.exitCode = 1
})
