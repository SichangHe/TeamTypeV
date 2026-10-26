// SPDX-License-Identifier: AGPL-3.0-or-later
const assert = require("node:assert/strict")
const fs = require("node:fs")
const path = require("node:path")
const vm = require("node:vm")
const ts = require("typescript")

const source = fs.readFileSync(process.argv[2] ?? path.join(__dirname, "../src/extension.ts"), "utf8")
const parsed = ts.createSourceFile("extension.ts", source, ts.ScriptTarget.Latest, true)
const names = new Set(["processEditFromDaemon", "processUserEdit", "processLocalEdit"])
const functions = parsed.statements.filter(node => ts.isFunctionDeclaration(node) && names.has(node.name.text))
const compiled = ts.transpileModule(functions.map(node => node.getText(parsed)).join("\n"), {
    compilerOptions: {target: ts.ScriptTarget.ES2022},
}).outputText

async function scenario(applied, events, expectedDaemonRevision, expectedSent) {
    const uri = "file:///note.txt"
    const sent = []
    const document = {
        version: 1,
        text: "base",
        getText() { return this.text },
        save: async () => true,
    }
    const client = {
        ot_states: {[uri]: {revision: {daemon: 0, editor: 0}, content: ["base"]}},
        connection: {sendRequest: (_type, edit) => { sent.push(edit); return Promise.resolve() }},
    }
    const context = vm.createContext({
        mutex: {runExclusive: callback => callback()},
        pendingRemote: null,
        rememberNativeChange() {},
        documentForUri: () => document,
        protocolUri: () => uri,
        getLines: doc => doc.text.split("\n"),
        teamtypevDeltasToVSCodeTextEdits: () => [],
        contentAfterEdits: () => "xbase",
        clientsForDocument: () => [client],
        updateContents: () => { client.ot_states[uri].content = document.text.split("\n") },
        vsCodeChangeEventToTeamtypevEdits: (_client, event) => [{
            uri, revision: client.ot_states[uri].revision.daemon,
            delta: event.contentChanges.map(change => ({replacement: change.text})),
        }],
        debug() {},
        editType: "edit",
        vscode: {window: {showErrorMessage(message) { throw new Error(message) }}},
        applyEdit: async () => {
            for (const [text, inserted] of events) {
                document.text = text
                document.version++
                context.processUserEdit({document, contentChanges: [{text: inserted}]})
            }
            return applied
        },
    })
    vm.runInContext(compiled, context)
    await context.processEditFromDaemon(client, {uri, revision: 0, delta: []})
    assert.equal(client.ot_states[uri].revision.daemon, expectedDaemonRevision)
    assert.deepEqual(sent.filter(edit => edit.delta.length).map(edit => [edit.revision, edit.delta[0].replacement]), expectedSent)
    assert.deepEqual(client.ot_states[uri].content, [document.text])
}

async function main() {
    await scenario(false, [["xbase", "x"]], 0, [[0, "x"]])
    await scenario(false, [["xbase", "x"], ["xybase", "y"]], 0, [[0, "x"], [0, "y"]])
    await scenario(true, [["xbase", "x"], ["xybase", "y"]], 1, [[1, "y"]])
    console.log("remote apply regressions passed: failed identical insertion, queued local edits, successful remote then local")
}
main().catch(error => { console.error(error); process.exitCode = 1 })
