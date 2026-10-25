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
async function waitFor(what: string, check: () => boolean | PromiseLike<boolean>, timeoutMs = 60000) {
    const deadline = Date.now() + timeoutMs
    while (!(await check())) {
        assert.ok(Date.now() < deadline, `Timed out waiting for: ${what}`)
        await sleep(200)
    }
}

const N_ROUNDS = 20
const EMACS_IMAGE = "silex/emacs:29"
/** Evaluates one expression per `cmd.N` file in `DIR` and writes its value to `out.N`. */
const EMACS_DRIVER = `
(let ((n 0) (dir (getenv "DIR")))
  (while t
    (let ((command (format "%s/cmd.%d" dir n)))
      (if (file-exists-p command)
          (let ((value (eval (read (with-temp-buffer (insert-file-contents command) (buffer-string))))))
            (write-region (format "%s" value) nil (format "%s/out.%d.tmp" dir n))
            (rename-file (format "%s/out.%d.tmp" dir n) (format "%s/out.%d" dir n))
            (setq n (1+ n)))
        (accept-process-output nil 0.05)))))
`

/**
 * Live trial with three people in one session: VS Code on the sharing daemon in `a`, a headless
 * Neovim on a joining daemon in `b`, and an Emacs (docker image `silex/emacs:29`) on a joining
 * daemon in `c`. Uses `TEAMTYPE_BINARY`, or else the repo's `target/debug/teamtype`.
 * Needs `nvim` and `docker`.
 */
suite("Extension Test Suite", () => {
    const repo = path.resolve(__dirname, "../../..")
    const bin = process.env.TEAMTYPE_BINARY ?? path.join(repo, "target/debug/teamtype")
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "teamtype-vscode-"))
    const [dirA, dirB, dirC] = ["a", "b", "c"].map((name) => path.join(root, name))
    const [fileA, fileB, fileC] = [dirA, dirB, dirC].map((dir) => path.join(dir, "file.txt"))
    const children: cp.ChildProcess[] = []
    const nvimSocket = path.join(root, "b.nvim")
    let doc: vscode.TextDocument
    let editor: vscode.TextEditor
    let daemonC: cp.ChildProcess
    let emacsDir = ""
    let nEmacsStarts = 0
    let nEmacsCommands = 0
    let emacsProcess: cp.ChildProcess | undefined

    const spawnDaemon = (dir: string, args: string[]) => {
        const fd = fs.openSync(`${dir}.log`, "a")
        const child = cp.spawn(bin, args, {cwd: dir, stdio: ["ignore", fd, fd]})
        children.push(child)
        return child
    }
    const run = (command: string, args: string[]) =>
        new Promise<string>((resolve, reject) =>
            cp.execFile(command, args, (error, stdout) => (error ? reject(error) : resolve(stdout))),
        )
    const nvimExpr = (expr: string) => run("nvim", ["--server", nvimSocket, "--remote-expr", expr])
    const emacsContainer = () => `teamtype-emacs-${process.pid}-${nEmacsStarts}`
    const startEmacs = async () => {
        nEmacsStarts++
        nEmacsCommands = 0
        emacsDir = path.join(root, `emacs.${nEmacsStarts}`)
        fs.mkdirSync(emacsDir)
        fs.writeFileSync(path.join(emacsDir, "driver.el"), `(find-file "${fileC}")\n${EMACS_DRIVER}`)
        const uid = `${process.getuid?.()}:${process.getgid?.()}`
        const fd = fs.openSync(`${emacsDir}.log`, "a")
        // The work directory keeps its path because the daemon rejects files outside its directory.
        const args = [
            "run",
            "--rm",
            "--name",
            emacsContainer(),
            "--user",
            uid,
            "-e",
            "HOME=/tmp",
            "-e",
            `DIR=${emacsDir}`,
        ]
        args.push("-v", `${bin}:/usr/local/bin/teamtype:ro`, "-v", `${root}:${root}`)
        args.push("-v", `${path.join(repo, "emacs-plugin")}:/plugin:ro`, EMACS_IMAGE)
        args.push("emacs", "--batch", "-L", "/plugin", "-l", "teamtype", "-l", path.join(emacsDir, "driver.el"))
        if (process.env.TEAMTYPE_EMACS_BINARY) {
            emacsProcess = cp.spawn(
                process.env.TEAMTYPE_EMACS_BINARY,
                [
                    "--batch",
                    "-Q",
                    "-L",
                    path.join(repo, "emacs-plugin"),
                    "-l",
                    "teamtype",
                    "-l",
                    path.join(emacsDir, "driver.el"),
                ],
                {stdio: ["ignore", fd, fd], env: {...process.env, DIR: emacsDir}},
            )
            children.push(emacsProcess)
        } else {
            children.push(cp.spawn("docker", args, {stdio: ["ignore", fd, fd]}))
        }
        await waitFor("Emacs tracks the file", async () => (await emacsEval("(and teamtype--client t)")) === "t")
    }
    const stopEmacs = () => (emacsProcess ? stopChild(emacsProcess) : run("docker", ["rm", "-f", emacsContainer()]))
    const stopChild = (child: cp.ChildProcess) => {
        if (child.exitCode !== null || child.signalCode !== null) return Promise.resolve()
        return new Promise<void>((resolve) => {
            let settled = false
            const finish = () => {
                if (settled) return
                settled = true
                clearTimeout(timer)
                resolve()
            }
            const timer = setTimeout(() => {
                child.kill("SIGKILL")
                finish()
            }, 5000)
            child.once("close", finish)
            child.once("exit", finish)
            child.once("error", finish)
            child.kill()
        })
    }
    /** Evaluates `expr` in the Emacs buffer of the shared file and returns its printed value. */
    const emacsEval = async (expr: string) => {
        const n = nEmacsCommands++
        const command = path.join(emacsDir, `cmd.${n}`)
        fs.writeFileSync(`${command}.tmp`, `(with-current-buffer (find-buffer-visiting "${fileC}") ${expr})`)
        fs.renameSync(`${command}.tmp`, command)
        const out = path.join(emacsDir, `out.${n}`)
        await waitFor(`Emacs answers ${expr}`, () => fs.existsSync(out))
        return fs.readFileSync(out, "utf8")
    }
    const typeLines = {
        vscode: async (prefix: string) => {
            for (let round = 0; round < N_ROUNDS; round++) {
                while (!(await editor.edit((e) => e.insert(new vscode.Position(1, 0), `${prefix}-${round}\n`)))) {
                    await sleep(10)
                }
                await sleep(20)
            }
        },
        nvim: async (prefix: string) => {
            for (let round = 0; round < N_ROUNDS; round++) {
                await nvimExpr(`nvim_buf_set_lines(0, 1, 1, 0, ['${prefix}-${round}'])`)
            }
        },
        emacs: async (prefix: string) => {
            for (let round = 0; round < N_ROUNDS; round++) {
                await emacsEval(
                    `(save-excursion (goto-char (point-min)) (forward-line 1) (insert "${prefix}-${round}\\n"))`,
                )
            }
        },
    }
    /**
     * Passes once all three editors, and the file on each daemon's disk, show the same text with
     * `count` lines matching `pattern`.
     */
    const editorsAgreeWith = async (what: string, pattern: RegExp, count: number) => {
        let texts: string[] = []
        try {
            await waitFor(what, async () => {
                texts = [
                    doc.getText(),
                    await nvimExpr(
                        'luaeval(\'table.concat(require("teamtype.changetracker").get_all_lines_respecting_eol(0), "\\n")\')',
                    ),
                    await emacsEval("(buffer-string)"),
                ]
                texts.push(...[fileA, fileB, fileC].map((file) => fs.readFileSync(file, "utf8")))
                return (texts[0].match(pattern) ?? []).length === count && texts.every((text) => text === texts[0])
            })
        } catch (error) {
            const counts = texts.map((text) => (text.match(pattern) ?? []).length)
            console.log(JSON.stringify({what, texts}))
            throw new Error(`${error}; lines matching in VS Code, Neovim, Emacs, disk a, b, c: ${counts}`)
        }
    }

    suiteSetup(async function () {
        this.timeout(180000)
        console.log(`TeamTypeV live work: ${root}`)
        assert.ok(fs.existsSync(bin), `teamtype binary not found: ${bin}`)
        for (const dir of [dirA, dirB, dirC]) {
            fs.mkdirSync(path.join(dir, ".teamtype"), {recursive: true})
        }
        fs.writeFileSync(path.join(dirA, "file.txt"), "seed\n")
        spawnDaemon(dirA, ["share", "--no-join-code", "--show-secret-address"])
        let addr: string | undefined
        await waitFor("sharing daemon prints its peer address", () => {
            addr = fs.readFileSync(`${dirA}.log`, "utf8").match(/peer=\S+/)?.[0]
            return addr !== undefined
        })
        for (const dir of [dirB, dirC]) {
            fs.writeFileSync(path.join(dir, ".teamtype", "config"), addr + "\n")
        }
        spawnDaemon(dirB, ["join"])
        daemonC = spawnDaemon(dirC, ["join"])
        await waitFor("joining daemons receive file.txt", () => fs.existsSync(fileB) && fs.existsSync(fileC))
        // The extension spawns plain `teamtype client`.
        process.env.PATH = `${path.dirname(bin)}${path.delimiter}${process.env.PATH}`
        doc = await vscode.workspace.openTextDocument(path.join(dirA, "file.txt"))
        editor = await vscode.window.showTextDocument(doc)
    })

    suiteTeardown(async function () {
        this.timeout(30000)
        if (nEmacsStarts) await stopEmacs().catch(() => undefined)
        await Promise.all(children.map(stopChild))
        if (!process.env.TEAMTYPE_KEEP_TEST_WORK) fs.rmSync(root, {recursive: true, force: true})
    })

    test("edits sync between VS Code and a second daemon", async function () {
        this.timeout(240000)
        const extension = vscode.extensions.getExtension("SichangHe.teamtype")
        assert.ok(extension, "TeamTypeV extension is not installed in the test host")
        await extension.activate()
        await waitFor("VS Code uses the daemon filesystem", () =>
            vscode.workspace.textDocuments.some(
                (candidate) => candidate.uri.scheme === "teamtype" && candidate.uri.path === fileA,
            ),
        )
        doc = vscode.workspace.textDocuments.find(
            (candidate) => candidate.uri.scheme === "teamtype" && candidate.uri.path === fileA,
        )!
        editor = await vscode.window.showTextDocument(doc)
        assert.ok((await vscode.commands.getCommands(true)).includes("teamtype.showCursors"))
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

    test("VS Code, Neovim, and Emacs type at once", async function () {
        if (process.env.TEAMTYPE_SKIP_EMACS) this.skip()
        this.timeout(300000)
        const nvimArgs = ["--headless", "--clean", "-n", "--listen", nvimSocket]
        nvimArgs.push("--cmd", `set runtimepath^=${path.join(repo, "nvim-plugin")}`, "file.txt")
        children.push(
            cp.spawn("nvim", nvimArgs, {cwd: dirB, stdio: "ignore", env: {...process.env, TEAMTYPE_BINARY: bin}}),
        )
        await waitFor("Neovim starts", () => fs.existsSync(nvimSocket))
        await startEmacs()
        await sleep(2000)

        await Promise.all([typeLines.vscode("v"), typeLines.nvim("n"), typeLines.emacs("e")])
        await editorsAgreeWith("every editor holds every typed line", /^[vne]-\d+$/gm, 3 * N_ROUNDS)
    })

    test("shared saves retain undo and unshared files retain native saves", async function () {
        this.timeout(60000)
        await vscode.window.showTextDocument(doc)
        const before = doc.getText()
        assert.ok(await editor.edit((edit) => edit.insert(new vscode.Position(0, 0), "undo-line\n")))
        await waitFor("shared save settles", () => doc.save())
        assert.strictEqual(doc.isDirty, false)
        await vscode.commands.executeCommand("undo")
        await waitFor(
            "undo reaches both daemons",
            () =>
                doc.getText() === before &&
                fs.readFileSync(fileA, "utf8") === before &&
                fs.readFileSync(fileB, "utf8") === before,
        )
        await vscode.commands.executeCommand("redo")
        await waitFor("redo reaches disk once", () => fs.readFileSync(fileA, "utf8") === `undo-line\n${before}`)
        await waitFor("redo saves", () => doc.save())
        assert.strictEqual(doc.isDirty, false)

        const unsharedFile = path.join(root, "unshared.txt")
        fs.writeFileSync(unsharedFile, "unshared\n")
        const unshared = await vscode.workspace.openTextDocument(unsharedFile)
        const edit = new vscode.WorkspaceEdit()
        edit.insert(unshared.uri, new vscode.Position(0, 0), "native\n")
        assert.ok(await vscode.workspace.applyEdit(edit))
        assert.ok(await unshared.save())
        assert.strictEqual(unshared.uri.scheme, "file")
        assert.strictEqual(fs.readFileSync(unsharedFile, "utf8"), "native\nunshared\n")
    })

    for (const editorName of ["VS Code", "Emacs"])
        test(`outside writes, checkout, and pull survive typing and saves in an open ${editorName} buffer`, async function () {
            if (editorName === "Emacs" && process.env.TEAMTYPE_SKIP_EMACS) this.skip()
            this.timeout(180000)
            const localDir = editorName === "Emacs" ? dirC : dirA
            const localFile = path.join(localDir, "file.txt")
            const bufferText = async () => (editorName === "Emacs" ? emacsEval("(buffer-string)") : doc.getText())
            const saveBuffer = async () =>
                editorName === "Emacs"
                    ? (await emacsEval("(progn (save-buffer) (not (buffer-modified-p)))")) === "t"
                    : doc.save()
            const git = (...args: string[]) => run("git", ["-C", localDir, ...args])
            await saveBuffer()
            await git("init", "-b", "main")
            await git("config", "user.name", "TeamTypeV Test")
            await git("config", "user.email", "test@example.invalid")
            await git("add", "file.txt")
            await git("commit", "-m", "initial")
            const initial = await bufferText()
            const upstream = path.join(root, `upstream-${editorName}`)
            await run("git", ["clone", localDir, upstream])
            await run("git", ["-C", upstream, "config", "user.name", "TeamTypeV Test"])
            await run("git", ["-C", upstream, "config", "user.email", "test@example.invalid"])
            await git("remote", "add", "upstream", upstream)

            const typingAndSaving = async (prefix: string) => {
                for (let n = 0; n < 12; n++) {
                    if (editorName === "Emacs") {
                        await emacsEval(`(progn (goto-char (point-min)) (insert "${prefix}-${n}\\n"))`)
                    } else {
                        while (
                            !(await editor.edit((edit) => edit.insert(new vscode.Position(0, 0), `${prefix}-${n}\n`)))
                        ) {
                            await sleep(10)
                        }
                    }
                    await waitFor("daemon save succeeds", saveBuffer)
                }
            }
            const checkLines = async (prefix: string, outside: string) => {
                try {
                    await waitFor(`${prefix} converges with disk and the other editors`, async () => {
                        const content = await bufferText()
                        return (
                            content === doc.getText() &&
                            [fileA, fileB, fileC].every((file) => content === fs.readFileSync(file, "utf8")) &&
                            content.includes(outside)
                        )
                    })
                } catch (error) {
                    console.log(
                        JSON.stringify({
                            buffer: doc.getText(),
                            diskA: fs.readFileSync(fileA, "utf8"),
                            diskB: fs.readFileSync(fileB, "utf8"),
                        }),
                    )
                    throw error
                }
                for (let n = 0; n < 12; n++) {
                    assert.strictEqual(
                        doc
                            .getText()
                            .split("\n")
                            .filter((line) => line === `${prefix}-${n}`).length,
                        1,
                    )
                }
                assert.strictEqual(
                    doc
                        .getText()
                        .split("\n")
                        .filter((line) => line === outside).length,
                    1,
                )
                assert.ok(await saveBuffer(), "saved buffer shows as saved")
            }

            const suffix = editorName === "Emacs" ? "-emacs" : ""
            const typing = typingAndSaving(`outside-typing${suffix}`)
            fs.appendFileSync(localFile, `outside-line${suffix}\n`)
            await typing
            await checkLines(`outside-typing${suffix}`, `outside-line${suffix}`)
            await git("add", "file.txt")
            await git("commit", "-m", "typing and outside write")

            await git("branch", "checkout-target")
            await git("switch", "checkout-target")
            fs.appendFileSync(localFile, `checkout-line${suffix}\n`)
            await waitFor("branch change reaches the editor", async () =>
                (await bufferText()).includes(`checkout-line${suffix}`),
            )
            await git("add", "file.txt")
            await git("commit", "-m", "checkout text")
            await git("switch", "main")
            await waitFor(
                "switch to main reaches the editor",
                async () => !(await bufferText()).includes(`checkout-line${suffix}`),
            )
            const checkout = git("checkout", "--force", "checkout-target")
            const checkoutTyping = typingAndSaving(`checkout-typing${suffix}`)
            await checkout
            await checkoutTyping
            await checkLines(`checkout-typing${suffix}`, `checkout-line${suffix}`)
            await git("add", "file.txt")
            await git("commit", "-m", "checkout typing")

            await run("git", ["-C", upstream, "fetch", "origin"])
            await run("git", ["-C", upstream, "reset", "--hard", "origin/checkout-target"])
            fs.writeFileSync(path.join(upstream, "file.txt"), (await bufferText()) + `pull-line${suffix}\n`)
            await run("git", ["-C", upstream, "add", "file.txt"])
            await run("git", ["-C", upstream, "commit", "-m", "pull text"])
            fs.writeFileSync(
                path.join(localDir, ".git", "hooks", "post-merge"),
                "#!/bin/sh\ntouch .teamtype/pull-started\nwhile [ ! -f .teamtype/typing-started ]; do sleep 0.01; done\n",
                {mode: 0o755},
            )
            const pull = git("pull", "--ff-only", "upstream", "main")
            await waitFor("pull passes its dirty-worktree check", () =>
                fs.existsSync(path.join(localDir, ".teamtype", "pull-started")),
            )
            const pullTyping = typingAndSaving(`pull-typing${suffix}`)
            fs.writeFileSync(path.join(localDir, ".teamtype", "typing-started"), "")
            await pull
            await pullTyping
            await checkLines(`pull-typing${suffix}`, `pull-line${suffix}`)
            assert.ok(doc.getText().includes(initial.trimEnd()), "initial text survives")
        })

    test("the Emacs person drops out and returns while the others type", async function () {
        if (process.env.TEAMTYPE_SKIP_EMACS) this.skip()
        this.timeout(300000)
        const others = Promise.all([typeLines.vscode("away-v"), typeLines.nvim("away-n")])
        await sleep(300)
        await stopEmacs()
        daemonC.kill()
        await waitFor("daemon C stops", () => daemonC.exitCode !== null || daemonC.signalCode !== null)
        fs.rmSync(path.join(dirC, ".teamtype", "socket"), {force: true})
        await others

        daemonC = spawnDaemon(dirC, ["join"])
        await waitFor("daemon C returns", () => fs.existsSync(path.join(dirC, ".teamtype", "socket")))
        await startEmacs()
        await typeLines.emacs("back-e")
        await editorsAgreeWith("lines typed during the absence reach everyone once", /^away-[vn]-\d+$/gm, 2 * N_ROUNDS)
        await editorsAgreeWith("lines typed after the return reach everyone", /^back-e-\d+$/gm, N_ROUNDS)
    })
    test("an agent edits while Neovim and Emacs type and VS Code watches", async function () {
        if (process.env.TEAMTYPE_SKIP_EMACS) this.skip()
        this.timeout(300000)
        const typing = Promise.all([typeLines.nvim("agent-n"), typeLines.emacs("agent-e")])
        // The agent reads the file from disk, and rereads and retries when it changed under it, as
        // a real agent would.
        await waitFor("the agent edit is accepted", async () => {
            const snapshot = fs.readFileSync(fileC, "utf8")
            const args = ["agent-edit", "--directory", dirC, "--file", "file.txt"]
            args.push("--old", snapshot, "--new", snapshot + "agent-line\n")
            return run(bin, args).then(
                () => true,
                () => false,
            )
        })
        await typing
        await editorsAgreeWith("the agent line reaches every editor", /^agent-line$/gm, 1)
        await editorsAgreeWith("lines typed next to the agent reach everyone", /^agent-[ne]-\d+$/gm, 2 * N_ROUNDS)
    })
})
