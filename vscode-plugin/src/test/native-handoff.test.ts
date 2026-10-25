import * as assert from "assert"
import * as cp from "child_process"
import * as fs from "fs"
import * as os from "os"
import * as path from "path"
import * as vscode from "vscode"
import {openSharedDocument} from "../extension"

suite("Native tab handoff", () => {
    for (const outside of ["", "outside\n"]) {
        test(`transfers dirty native text without a native save or close prompt${outside ? " and preserves outside additions" : ""}`, async function () {
            this.timeout(30000)
            const root = fs.mkdtempSync(path.join(os.tmpdir(), "teamtype-handoff-"))
            const file = path.join(root, "note.txt")
            const bin = process.env.TEAMTYPE_BINARY ?? path.resolve(__dirname, "../../../target/debug/teamtype")
            process.env.PATH = `${path.dirname(bin)}${path.delimiter}${process.env.PATH}`
            fs.writeFileSync(file, "base\n")
            const extension = vscode.extensions.getExtension("SichangHe.teamtype")!
            await extension.activate()
            const native = await vscode.workspace.openTextDocument(file)
            await vscode.window.showTextDocument(native)
            const localEdit = new vscode.WorkspaceEdit()
            localEdit.insert(native.uri, new vscode.Position(0, 0), "unsaved 🐟\n")
            assert.ok(await vscode.workspace.applyEdit(localEdit))
            assert.ok(native.isDirty)
            if (outside) fs.writeFileSync(file, `base\n${outside}`)
            fs.mkdirSync(path.join(root, ".teamtype"))
            const log = fs.openSync(path.join(root, ".teamtype", "handoff.log"), "w")
            const daemon = cp.spawn(bin, ["share", "--no-join-code"], {cwd: root, stdio: ["ignore", log, log]})
            fs.closeSync(log)
            let nativeSaves = 0
            const saved = vscode.workspace.onDidSaveTextDocument((document) => {
                if (document.uri.toString() === native.uri.toString()) nativeSaves++
            })
            const waitFor = async (check: () => boolean) => {
                const deadline = Date.now() + 15000
                while (!check()) {
                    assert.ok(Date.now() < deadline, "handoff did not finish")
                    await new Promise((resolve) => setTimeout(resolve, 50))
                }
            }
            try {
                await waitFor(() => fs.existsSync(path.join(root, ".teamtype", "socket")))
                let timer: ReturnType<typeof setTimeout> | undefined
                try {
                    await Promise.race([
                        openSharedDocument("teamtype", native, root),
                        new Promise((_, reject) => {
                            timer = setTimeout(
                                () => reject(new Error("native handoff blocked on a close/save prompt")),
                                5000,
                            )
                        }),
                    ])
                } finally {
                    if (timer) clearTimeout(timer)
                }
                const shared = vscode.workspace.textDocuments.find(
                    (document) => document.uri.scheme === "teamtype" && document.uri.fsPath === file,
                )!
                assert.ok(shared)
                await waitFor(
                    () =>
                        shared.getText() === `unsaved 🐟\nbase\n${outside}` &&
                        fs.readFileSync(file, "utf8") === shared.getText(),
                )
                assert.strictEqual(nativeSaves, 0)
                assert.ok(
                    !vscode.window.tabGroups.all
                        .flatMap((group) => group.tabs)
                        .some(
                            (tab) =>
                                tab.input instanceof vscode.TabInputText &&
                                tab.input.uri.toString() === native.uri.toString(),
                        ),
                )
                await shared.save()
                await vscode.commands.executeCommand("workbench.action.closeActiveEditor")
            } finally {
                saved.dispose()
                const exited = new Promise<void>((resolve) => daemon.once("exit", () => resolve()))
                if (daemon.exitCode === null && daemon.signalCode === null) {
                    daemon.kill("SIGTERM")
                    await exited
                }
                fs.rmSync(root, {recursive: true, force: true})
            }
        })
    }
})
