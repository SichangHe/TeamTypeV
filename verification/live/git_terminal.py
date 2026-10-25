#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Sichang He
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Real-daemon shell activation and PTY Git regressions; prints only failures."""

import errno
import fcntl
import os
from pathlib import Path
import pty
import re
import select
import shlex
import shutil
import signal
import struct
import subprocess
import tempfile
import termios
import time
import unittest


ROOT = Path(__file__).resolve().parents[2]
BINARY = Path(
    os.environ.get("TEAMTYPE_BINARY", ROOT / "target/debug/teamtype")
).resolve()


def run(*args, cwd, **kwargs):
    return subprocess.run(
        args, cwd=cwd, check=True, capture_output=True, timeout=30, **kwargs
    )


def eventually(check):
    deadline = time.monotonic() + 45
    while time.monotonic() < deadline:
        if check():
            return
        time.sleep(0.1)
    raise AssertionError("Timed out waiting for daemon")


class TerminalGit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = Path(tempfile.mkdtemp(prefix="teamtype-terminal-"))
        cls.host = cls.work / "host"
        cls.join = cls.work / "join ' quoted \\ path"
        cls.processes = []
        cls.logs = []
        cls.preserve_logs = False
        cls.addClassCleanup(cls.cleanup)
        for directory in (cls.host, cls.join):
            (directory / ".teamtype").mkdir(parents=True)
        run("git", "init", "-qb", "master", cwd=cls.host)
        run("git", "config", "user.name", "Test", cwd=cls.host)
        run("git", "config", "user.email", "test@example.test", cwd=cls.host)
        (cls.host / "file").write_text("initial\n")
        run("git", "add", "file", cwd=cls.host)
        run("git", "commit", "-qm", "initial", cwd=cls.host)
        cls.start(cls.host, "share", "--no-join-code", "--show-secret-address")
        host_log = cls.work / "host.log"
        eventually(lambda: re.search(r"peer=\S+", host_log.read_text()))
        address = re.search(r"peer=\S+", host_log.read_text())[0]
        (cls.join / ".teamtype/config").write_text(address + "\n")
        cls.start(cls.join, "join")
        eventually(lambda: (cls.join / "file").exists())
        cls.editor = cls.work / "editor"
        cls.editor.write_text(
            "#!/bin/sh\ntest -t 0 && test -t 1 && test -t 2 || exit 91\n"
            'printf "EDITOR_READY\\n"\nIFS= read -r message\nprintf "%s\\n" "$message" >"$1"\n'
        )
        cls.editor.chmod(0o755)
        run("git", "config", "core.editor", shlex.quote(str(cls.editor)), cwd=cls.host)
        cls.pager = cls.work / "pager"
        cls.pager.write_text(
            "#!/bin/sh\ntest -t 1 && test -t 2 || exit 92\n"
            'printf "PAGER_READY\\n"\nIFS= read -r answer </dev/tty\ncat\n'
        )
        cls.pager.chmod(0o755)
        run("git", "config", "core.pager", shlex.quote(str(cls.pager)), cwd=cls.host)

    @classmethod
    def start(cls, directory, *args):
        log = (cls.work / ("host.log" if directory == cls.host else "join.log")).open(
            "w"
        )
        cls.logs.append(log)
        cls.processes.append(
            subprocess.Popen(
                [BINARY, *args],
                cwd=directory,
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=log,
            )
        )

    @classmethod
    def cleanup(cls):
        for process in cls.processes:
            process.terminate()
        for process in cls.processes:
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
        for log in cls.logs:
            log.close()
        if cls.preserve_logs:
            saved = Path(tempfile.mkdtemp(prefix="teamtype-terminal-failure-"))
            for name in ("host.log", "join.log"):
                shutil.copyfile(cls.work / name, saved / name)
            print(f"Daemon logs preserved in {saved}")
        shutil.rmtree(cls.work)

    def test_activation(self):
        for shell in ("bash", "zsh", "fish"):
            with self.subTest(shell=shell):
                self.assertIsNotNone(
                    shutil.which(shell), f"Missing required shell: {shell}"
                )
                environment = dict(
                    os.environ,
                    ACTIVATE=str(self.join / ".teamtype/activate"),
                    SHIM=str(self.join / ".teamtype/bin/git"),
                )
                if shell == "fish":
                    script = """
set old_path $PATH
source "$ACTIVATE.fish"; or exit 1
source "$ACTIVATE.fish"; or exit 2
test (command -s git) = "$SHIM"; or exit 3
test (git log -1 --format=%s) = initial; or exit 4
deactivate
test (string join : $PATH) = (string join : $old_path); or exit 5
functions -q deactivate; and exit 6
function deactivate; echo restored; end
source "$ACTIVATE.fish"; or exit 7
source "$ACTIVATE.fish"; or exit 8
deactivate
test (deactivate) = restored; or exit 9
exit 0
"""
                    command = [shell, "--no-config", "-c", script]
                else:
                    script = """
set -eu
old_path=$PATH
source "$ACTIVATE" || exit 1
source "$ACTIVATE" || exit 2
[ "$(command -v git)" = "$SHIM" ] || exit 3
[ "$(git log -1 --format=%s)" = initial ] || exit 4
deactivate
[ "$PATH" = "$old_path" ] || exit 5
typeset -f deactivate >/dev/null && exit 6
deactivate() { printf restored; }
source "$ACTIVATE" || exit 7
source "$ACTIVATE" || exit 8
deactivate
[ "$(deactivate)" = restored ] || exit 9
exit 0
"""
                    command = (
                        [shell, "-f", "-c", script]
                        if shell == "zsh"
                        else [shell, "--noprofile", "--norc", "-c", script]
                    )
                result = run(*command, cwd=self.join, env=environment)
                self.assertEqual(result.returncode, 0)

    def terminal(
        self,
        args,
        exchanges,
        expected_code=0,
        resize=None,
        no_ctty=False,
        timeout_s=30,
        signal_after_input=None,
    ):
        ready_read, ready_write = os.pipe()
        pid, master = pty.fork()
        if pid == 0:
            os.close(ready_write)
            os.read(ready_read, 1)
            os.close(ready_read)
            if no_ctty:
                signal.signal(signal.SIGHUP, signal.SIG_IGN)
                fcntl.ioctl(0, termios.TIOCNOTTY)
                signal.signal(signal.SIGHUP, signal.SIG_DFL)
            os.chdir(self.join)
            os.environ["TERM"] = "xterm-256color"
            if os.environ.get("TERMINAL_DIRECT"):
                os.execv(str(BINARY), [str(BINARY), "git", *args])
            script = "source .teamtype/activate; exec git " + shlex.join(args)
            os.execvp("bash", ["bash", "--noprofile", "--norc", "-c", script])
        output = bytearray()
        os.close(ready_read)
        before = termios.tcgetattr(master)
        os.set_blocking(master, False)
        os.write(ready_write, b"1")
        os.close(ready_write)
        deadline = time.monotonic() + timeout_s
        exchanges = list(exchanges)
        status = None
        waited = 0
        pending = bytearray()
        try:
            while time.monotonic() < deadline:
                readable, writable, _ = select.select(
                    [master], [master] if pending else [], [], 0.05
                )
                if readable:
                    try:
                        chunk = os.read(master, 65536)
                    except OSError as error:
                        if error.errno != errno.EIO:
                            raise
                        chunk = b""
                    output.extend(chunk)
                if writable:
                    count = os.write(master, pending[:4096])
                    del pending[:count]
                if exchanges and exchanges[0][0] in output:
                    _, answer = exchanges.pop(0)
                    if resize:
                        fcntl.ioctl(
                            master,
                            termios.TIOCSWINSZ,
                            struct.pack("HHHH", *resize, 0, 0),
                        )
                        os.kill(pid, signal.SIGWINCH)
                        resize = None
                    if callable(answer):
                        answer()
                    elif isinstance(answer, int):
                        os.kill(pid, answer)
                    else:
                        pending.extend(answer)
                if signal_after_input is not None and not exchanges and not pending:
                    os.kill(pid, signal_after_input)
                    signal_after_input = None
                waited, status = os.waitpid(pid, os.WNOHANG)
                if waited:
                    break
            else:
                self.fail(f"PTY command hung: {args!r}: {bytes(output)!r}")
            self.assertFalse(exchanges, bytes(output))
            self.assertEqual(
                os.waitstatus_to_exitcode(status), expected_code, bytes(output)
            )
            self.assertEqual(
                termios.tcgetattr(master), before, "Client left terminal modes changed"
            )
            return bytes(output)
        except Exception:
            type(self).preserve_logs = True
            raise
        finally:
            if status is None or status == 0 and not waited:
                os.kill(pid, signal.SIGKILL)
                os.waitpid(pid, 0)
            os.close(master)

    def test_add_patch(self):
        (self.join / "file").write_text("patched\n")
        self.terminal(["add", "-p", "file"], [(b"Stage this hunk", b"y\n")])
        self.assertEqual(
            run("git", "show", ":file", cwd=self.host).stdout, b"patched\n"
        )

    def test_commit_editor(self):
        output = self.terminal(
            ["commit", "--allow-empty"], [(b"EDITOR_READY", b"interactive commit\n")]
        )
        self.assertIn(b"interactive commit", output)
        self.assertEqual(
            run("git", "log", "-1", "--format=%s", cwd=self.host).stdout.strip(),
            b"interactive commit",
        )

    def test_colors(self):
        run("git", "config", "color.ui", "auto", cwd=self.host)
        output = self.terminal(
            ["--no-pager", "log", "-1", "--format=%C(auto)%h%Creset", "--no-patch"], []
        )
        self.assertIn(b"\x1b[", output)

    def test_pager(self):
        output = self.terminal(
            ["--paginate", "log", "-1", "--oneline"], [(b"PAGER_READY", b"\n")]
        )
        self.assertIn(b"interactive commit", output)

    def test_resize_and_interrupt(self):
        helper = self.work / "resize"
        helper.write_text(
            '#!/bin/sh\nprintf "RESIZE_READY\\n"\n'
            "trap 'stty size; exit 0' WINCH\nwhile :; do sleep 0.1; done\n"
        )
        helper.chmod(0o755)
        run(
            "git",
            "config",
            "alias.resize-test",
            "!" + shlex.quote(str(helper)),
            cwd=self.host,
        )
        output = self.terminal(
            ["resize-test"], [(b"RESIZE_READY", b"")], resize=(37, 99)
        )
        self.assertIn(b"37 99", output)
        run(
            "git",
            "config",
            "alias.interrupt-test",
            "!printf 'INTERRUPT_READY\\n'; sleep 30",
            cwd=self.host,
        )
        self.terminal(
            ["interrupt-test"], [(b"INTERRUPT_READY", b"\x03")], expected_code=130
        )

    def test_external_signal(self):
        run(
            "git",
            "config",
            "alias.signal-test",
            "!printf 'SIGNAL_READY\\n'; sleep 30",
            cwd=self.host,
        )
        self.terminal(
            ["signal-test"], [(b"SIGNAL_READY", signal.SIGTERM)], expected_code=143
        )

    def test_full_duplex(self):
        run(
            "git",
            "config",
            "alias.duplex-test",
            "!stty raw -echo; printf BULK_READY; head -c 262144",
            cwd=self.host,
        )
        payload = bytes(range(256)) * 1024
        output = self.terminal(["duplex-test"], [(b"BULK_READY", payload)])
        self.assertEqual(output, b"BULK_READY" + payload)

    def test_signal_with_blocked_input(self):
        run(
            "git",
            "config",
            "alias.blocked-input-test",
            "!stty raw -echo; printf BLOCKED_INPUT_READY; exec sleep 20",
            cwd=self.host,
        )
        self.terminal(
            ["blocked-input-test"],
            [(b"BLOCKED_INPUT_READY", b"x" * 262144)],
            expected_code=143,
            signal_after_input=signal.SIGTERM,
            timeout_s=8,
        )
        self.terminal(["--no-pager", "status", "--porcelain"], [], timeout_s=5)

    def test_rejected_directory_override(self):
        self.terminal(["-C", "/", "status"], [], expected_code=129)

    def test_queued_interrupt(self):
        run(
            "git",
            "config",
            "alias.queue-blocker",
            "!printf 'BLOCKER_READY\\n'; sleep 30",
            cwd=self.host,
        )
        marker = self.work / "cancelled-command-ran"
        run(
            "git",
            "config",
            "alias.must-not-run",
            "!touch " + shlex.quote(str(marker)),
            cwd=self.host,
        )
        blocker = subprocess.Popen(
            [BINARY, "git", "queue-blocker"],
            cwd=self.host,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            self.assertTrue(
                select.select([blocker.stdout], [], [], 10)[0], "Blocker never started"
            )
            self.assertEqual(blocker.stdout.readline(), b"BLOCKER_READY\n")
            for answer in (b"\x03", signal.SIGINT):
                output = self.terminal(
                    ["must-not-run"],
                    [(b"Git queued behind:", answer)],
                    expected_code=130,
                    timeout_s=5,
                )
                self.assertIn(b"\r\n", output)
                self.assertIsNone(
                    blocker.poll(), "Queued cancellation stopped the active command"
                )
        finally:
            blocker.terminate()
            blocker.wait(timeout=5)
            blocker.stdout.close()
            blocker.stderr.close()
        run(str(BINARY), "git", "status", "--porcelain", cwd=self.host)
        self.assertFalse(marker.exists(), "Cancelled queued Git request executed")

    def test_no_controlling_terminal(self):
        self.terminal(["--no-pager", "status", "--porcelain"], [], no_ctty=True)

    def test_rebase_editor(self):
        run("git", "commit", "--allow-empty", "-qm", "rebase fixture", cwd=self.host)
        editor = self.work / "sequence-editor"
        editor.write_text('#!/bin/sh\nprintf "SEQUENCE_READY\\n"\nread -r answer\n')
        editor.chmod(0o755)
        run("git", "config", "sequence.editor", shlex.quote(str(editor)), cwd=self.host)
        self.terminal(["rebase", "-i", "HEAD~1"], [(b"SEQUENCE_READY", b"\n")])

    def test_z_disconnect(self):
        run(
            "git",
            "config",
            "alias.disconnect-test",
            "!printf 'DISCONNECT_READY\\n'; sleep 30",
            cwd=self.host,
        )
        self.terminal(
            ["disconnect-test"],
            [(b"DISCONNECT_READY", self.processes[1].terminate)],
            expected_code=1,
        )
        run(str(BINARY), "git", "status", "--porcelain", cwd=self.host)


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(TerminalGit)
    result = unittest.TestResult()
    suite.run(result)
    for test, failure in result.errors + result.failures:
        print(f"FAIL: {test}\n{failure}")
    raise SystemExit(not result.wasSuccessful())
