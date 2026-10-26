// SPDX-License-Identifier: AGPL-3.0-or-later
const assert = require("node:assert/strict")
const fs = require("node:fs")
const path = require("node:path")
const vm = require("node:vm")
const ts = require("typescript")

const source = fs.readFileSync(process.argv[2] ?? path.join(__dirname, "../src/extension.ts"), "utf8")
const parsed = ts.createSourceFile("extension.ts", source, ts.ScriptTarget.Latest, true)
const names = new Set(["openSharedDocument", "handoffDelta", "rememberNativeCleanContent", "rememberNativeChange"])
const functions = parsed.statements.filter(node => ts.isFunctionDeclaration(node) && names.has(node.name.text))
const compiled = ts.transpileModule(functions.map(node => node.getText(parsed).replace(/^export /, "")).join("\n"), {
    compilerOptions: {target: ts.ScriptTarget.ES2022},
}).outputText

async function scenario(knownBaseline, cleanReload = false) {
    const uri = {scheme: "file", fsPath: "/note.txt", with() {return this}, toString() {return "file:///note.txt"}}
    let originalText = cleanReload ? "base\n" : "typed\nbase\n"
    const original = {uri, isDirty: !cleanReload, version: 2, getText: () => originalText}
    const nativeCleanContents = new WeakMap()
    if (knownBaseline) nativeCleanContents.set(original, "base\n")
    const sent = []
    const sharedContents = new Map()
    let closed = false
    let readonly = false
    let copiedText = ""
    const shared = {uri, lineCount: 3, getText: () => copiedText, save() {}}
    const client = {ot_states: {}, connection: {sendRequest: async (method, params) => sent.push([method, params])}}
    const context = vm.createContext({
        nativeCleanContents,
        pendingNativeCleanContents: new WeakMap(),
        sharedContents,
        Buffer,
        TextDecoder,
        fs: {readFileSync: (_path, encoding) => encoding ? "base\noutside\n" : Buffer.from("base\noutside\n")},
        documentForUri: () => undefined,
        protocolUri: () => uri.toString(),
        findOrCreateClient: () => client,
        prepareNativeHandoff: async () => {
            readonly = true
            if (cleanReload) {
                originalText = "base\noutside\n"
                original.version++
                context.rememberNativeChange({document: original, contentChanges: [{}]})
            }
        },
        closeNativeDocument: async () => {closed = true},
        getLines: () => copiedText.split("\n"),
        Revision: class {daemon = 0; editor = 0},
        editType: "edit",
        debug() {},
        vscode: {
            Range: class {},
            WorkspaceEdit: class {replace(_uri, _range, text) {this.text = text}},
            window: {showErrorMessage() {}, showTextDocument: async () => {}},
            workspace: {
                onDidChangeTextDocument: () => ({dispose() {}}),
                openTextDocument: async () => {copiedText = Buffer.from(sharedContents.get(uri.toString())).toString(); return shared},
                applyEdit: async edit => {copiedText = edit.text; return true},
            },
        },
    })
    vm.runInContext(compiled, context)
    await context.openSharedDocument("teamtypev", original, "/")
    if (cleanReload) {
        assert.equal(sent.find(([method]) => method === "open")[1].content, "base\noutside\n")
        assert.equal(sent.filter(([method]) => method === "edit").length, 0)
        assert.equal(closed, true)
    } else if (knownBaseline) {
        assert.equal(sent.find(([method]) => method === "open")[1].content, "base\n")
        const delta = sent.find(([method]) => method === "edit")[1].delta[0]
        assert.equal(delta.replacement, "typed\n")
        assert.equal(delta.range.start.line, delta.range.end.line)
        assert.equal(delta.range.start.character, delta.range.end.character)
        assert.equal(closed, true)
    } else {
        assert.equal(sent.length, 0)
        assert.equal(closed, false)
        assert.equal(readonly, true)
        assert.equal(original.getText(), "typed\nbase\n")
    }
}

async function main() {
    await scenario(true)
    await scenario(false)
    await scenario(true, true)
    const nativeCleanContents = new WeakMap()
    const pendingNativeCleanContents = new WeakMap()
    let text = "base\n"
    const document = {uri: {scheme: "file"}, isDirty: false, getText: () => text}
    const context = vm.createContext({nativeCleanContents, pendingNativeCleanContents})
    vm.runInContext(compiled, context)
    context.rememberNativeCleanContent(document)
    text = "typed\nbase\n"
    context.rememberNativeChange({document, contentChanges: [{}]})
    document.isDirty = true
    context.rememberNativeChange({document, contentChanges: []})
    assert.equal(nativeCleanContents.get(document), "base\n")
    text = "base\n"
    document.isDirty = false
    context.rememberNativeCleanContent(document)
    text = "base\noutside\n"
    context.rememberNativeChange({document, contentChanges: [{}]})
    text = "typed\nbase\noutside\n"
    context.rememberNativeChange({document, contentChanges: [{}]})
    document.isDirty = true
    context.rememberNativeChange({document, contentChanges: []})
    assert.equal(nativeCleanContents.get(document), "base\noutside\n")
    console.log("native baseline regressions passed: clean base, unknown dirty base, delayed dirty event, reload then typing, clean reload during handoff")
}
main().catch(error => {console.error(error); process.exitCode = 1})
