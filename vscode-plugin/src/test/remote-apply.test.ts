import * as assert from "assert"
import * as vscode from "vscode"

suite("Workspace edit interleaving", () => {
    test("an identical local edit can arrive before a pending remote edit is rejected", async () => {
        const document = await vscode.workspace.openTextDocument({content: "base", language: "plaintext"})
        const observed: {content: string; version: number; remoteSettled: boolean}[] = []
        let remoteSettled = false
        const version = document.version
        const changed = vscode.workspace.onDidChangeTextDocument((event) => {
            if (event.document === document && event.contentChanges.length) {
                observed.push({content: document.getText(), version: document.version, remoteSettled})
            }
        })
        const local = new vscode.WorkspaceEdit()
        const remote = new vscode.WorkspaceEdit()
        local.insert(document.uri, new vscode.Position(0, 0), "x")
        remote.insert(document.uri, new vscode.Position(0, 0), "x")
        try {
            const localApplied = vscode.workspace.applyEdit(local)
            const remoteApplied = vscode.workspace.applyEdit(remote).then((result) => {
                remoteSettled = true
                return result
            })
            assert.strictEqual(await localApplied, true)
            assert.strictEqual(await remoteApplied, false)
            assert.deepStrictEqual(observed, [{content: "xbase", version: version + 1, remoteSettled: false}])
        } finally {
            changed.dispose()
        }
    })
})
