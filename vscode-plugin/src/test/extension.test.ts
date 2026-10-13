// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

import * as assert from "assert"
import * as cp from "child_process"
import * as fs from "fs"
import * as os from "os"
import * as path from "path"
import * as vscode from "vscode"

const sleep = (ms: number) => new Promise((resolve) => setTimeout(resolve, ms))

/** Polls `check` until it returns true; fails with `what` after `timeoutMs`. */
async function waitFor(what: string, check: () => boolean, timeoutMs = 60000) {
    const deadline = Date.now() + timeoutMs
    while (!check()) {
        assert.ok(Date.now() < deadline, `Timed out waiting for: ${what}`)
        await sleep(200)
    }
}

/**
 * Real end-to-end test: daemon A (opened in VS Code) shares `dir_a`, daemon B joins into `dir_b`.
 * Uses `TEAMTYPE_BINARY`, or else the repo's `target/debug/teamtype`.
 */
suite("Extension Test Suite", () => {
    const bin = process.env.TEAMTYPE_BINARY ?? path.resolve(__dirname, "../../../target/debug/teamtype")
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "teamtype-vscode-"))
    const dirA = path.join(root, "a")
    const dirB = path.join(root, "b")
    const daemons: cp.ChildProcess[] = []
    const logA = path.join(root, "a.log")
    const spawnDaemon = (dir: string, args: string[], log: string) => {
        const fd = fs.openSync(log, "w")
        const child = cp.spawn(bin, args, {cwd: dir, stdio: ["ignore", fd, fd]})
        daemons.push(child)
        return child
    }

    suiteSetup(async function () {
        this.timeout(120000)
        assert.ok(fs.existsSync(bin), `teamtype binary not found: ${bin}`)
        for (const dir of [dirA, dirB]) {
            fs.mkdirSync(path.join(dir, ".teamtype"), {recursive: true})
        }
        fs.writeFileSync(path.join(dirA, "file.txt"), "seed\n")
        spawnDaemon(dirA, ["share", "--no-join-code", "--show-secret-address"], logA)
        let addr: string | undefined
        await waitFor("sharing daemon prints its peer address", () => {
            addr = fs.readFileSync(logA, "utf8").match(/peer=\S+/)?.[0]
            return addr !== undefined
        })
        fs.writeFileSync(path.join(dirB, ".teamtype", "config"), addr + "\n")
        spawnDaemon(dirB, ["join"], path.join(root, "b.log"))
        await waitFor("joining daemon receives file.txt", () => fs.existsSync(path.join(dirB, "file.txt")))
        // The extension spawns plain `teamtype client`.
        process.env.PATH = `${path.dirname(bin)}${path.delimiter}${process.env.PATH}`
    })

    suiteTeardown(() => {
        daemons.forEach((d) => d.kill())
        fs.rmSync(root, {recursive: true, force: true})
    })

    test("edits sync between VS Code and a second daemon", async function () {
        this.timeout(240000)
        const extension = vscode.extensions.getExtension("teamtype.teamtype")
        assert.ok(extension, "Teamtype extension is not installed in the test host")
        await extension.activate()
        assert.ok((await vscode.commands.getCommands(true)).includes("teamtype.showCursors"))

        const doc = await vscode.workspace.openTextDocument(path.join(dirA, "file.txt"))
        const editor = await vscode.window.showTextDocument(doc)
        const fileB = path.join(dirB, "file.txt")
        const readB = () => fs.readFileSync(fileB, "utf8")

        // (1) VS Code -> daemon B's file on disk. Retry typing until the client has opened the file.
        let n = 0
        await waitFor("typed text reaches daemon B's file", () => {
            if (readB().includes("typed-in-vscode")) return true
            if (n++ % 25 === 0) {
                void editor.edit((e) => e.insert(new vscode.Position(0, 0), "typed-in-vscode\n"))
            }
            return false
        })

        // (2) Daemon B's file -> VS Code document.
        fs.writeFileSync(fileB, readB() + "written-in-b\n")
        await waitFor("daemon B's change appears in VS Code", () => doc.getText().includes("written-in-b"))
    })
    test("VS Code and a Neovim on the second daemon type at once", async function () {
        this.timeout(240000)
        const nRounds = 20
        const doc = await vscode.workspace.openTextDocument(path.join(dirA, "file.txt"))
        const editor = await vscode.window.showTextDocument(doc)
        const nvimSocket = path.join(root, "b.nvim")
        const nvimPlugin = path.resolve(__dirname, "../../../nvim-plugin")
        daemons.push(
            cp.spawn(
                "nvim",
                ["--headless", "--clean", "-n", "--listen", nvimSocket, "--cmd", `set runtimepath^=${nvimPlugin}`, "file.txt"],
                {cwd: dirB, stdio: "ignore", env: {...process.env, TEAMTYPE_BINARY: bin}},
            ),
        )
        await waitFor("Neovim starts", () => fs.existsSync(nvimSocket))
        const nvimExpr = (expr: string) =>
            new Promise<string>((resolve, reject) =>
                cp.execFile("nvim", ["--server", nvimSocket, "--remote-expr", expr], (error, stdout) =>
                    error ? reject(error) : resolve(stdout),
                ),
            )
        await sleep(2000)

        const typeInNvim = async () => {
            for (let round = 0; round < nRounds; round++) {
                await nvimExpr(`nvim_buf_set_lines(0, 1, 1, 0, ['n-${round}'])`)
            }
        }
        const typeInVscode = async () => {
            for (let round = 0; round < nRounds; round++) {
                while (!(await editor.edit((e) => e.insert(new vscode.Position(1, 0), `v-${round}\n`)))) {
                    await sleep(10)
                }
                await sleep(20)
            }
        }
        await Promise.all([typeInNvim(), typeInVscode()])

        const count = (pattern: RegExp) => (doc.getText().match(pattern) ?? []).length
        await waitFor("VS Code holds every line typed in both editors", () => {
            return count(/^n-\d+$/gm) === nRounds && count(/^v-\d+$/gm) === nRounds
        })
        let nvimText = ""
        const deadline = Date.now() + 60000
        while (nvimText !== doc.getText()) {
            assert.ok(Date.now() < deadline, "Neovim buffer and VS Code document differ")
            await sleep(200)
            nvimText = await nvimExpr('join(getline(1, "$"), "\\n") .. "\\n"')
        }
    })
})
