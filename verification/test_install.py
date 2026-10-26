#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Sichang He
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Exercise the installer with local archives and no network access."""
# unittest initializes per-test state in setUp, outside __init__.
# pyright: reportUninitializedInstanceVariable=false, reportImplicitOverride=false

import io
import fcntl
import os
from pathlib import Path
import pty
import select
import shutil
import subprocess
import tarfile
import tempfile
import termios
import time
import unittest


INSTALLER = Path(__file__).resolve().parents[1] / "install.sh"


class InstallTests(unittest.TestCase):
    temp: tempfile.TemporaryDirectory[str]
    root: Path
    bin: Path
    env: dict[str, str]

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="teamtypev-install-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        for command in (
            "tar",
            "gzip",
            "mkdir",
            "mv",
            "chmod",
            "mktemp",
            "rm",
            "sed",
            "grep",
            "dirname",
        ):
            executable = shutil.which(command, path=os.defpath)
            assert executable is not None, command
            (self.bin / command).symlink_to(executable)
        self.env = {
            **os.environ,
            "HOME": str(self.root / "home"),
            "PATH": str(self.bin),
            "TMPDIR": str(self.root),
            "TEST_ROOT": str(self.root),
            "TEST_OS": "Linux",
            "TEST_ARCH": "x86_64",
        }
        self.script(
            "uname",
            'case "$1" in -s) echo "$TEST_OS";; -m) echo "$TEST_ARCH";; *) exit 2;; esac\n',
        )
        payload = b'#!/bin/sh\necho "teamtypev test-version"\n'
        with tarfile.open(self.root / "release.tar.gz", "w:gz") as archive:
            member = tarfile.TarInfo("teamtypev")
            member.size = len(payload)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(payload))
        self.downloader("curl")
        _ = (self.root / "teamtypev.el").write_text("(provide 'teamtypev)\n")
        _ = (self.root / "teamtypev.vsix").write_bytes(b"local extension payload")
        with tarfile.open(self.root / "teamtypev-nvim.tar.gz", "w:gz") as archive:
            payload = b"vim.g.teamtypev_test_loaded = true\n"
            member = tarfile.TarInfo("plugin/teamtypev.lua")
            member.size = len(payload)
            archive.addfile(member, io.BytesIO(payload))

    def script(self, name: str, body: str) -> None:
        path = self.bin / name
        _ = path.write_text("#!/bin/sh\nset -eu\n" + body)
        path.chmod(0o755)

    def downloader(self, name: str) -> None:
        copy = shutil.which("cp")
        assert copy is not None
        if name == "curl":
            body = 'test "$1" = -fsSL\ntest "$3" = -o\nurl=$2\n'
            destination = '"$4"'
        else:
            body = 'test "$1" = -qO\nurl=$3\n'
            destination = '"$2"'
        body += """printf "%s\\n" "$url" > "$TEST_ROOT/url"
case "$url" in
*/teamtypev.el) asset=teamtypev.el ;;
*/teamtypev.vsix) asset=teamtypev.vsix ;;
*/teamtypev-nvim.tar.gz) asset=teamtypev-nvim.tar.gz ;;
*) asset=release.tar.gz ;;
esac
"""
        self.script(name, body + f'"{copy}" "$TEST_ROOT/$asset" {destination}\n')

    def run_install(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["/bin/sh", str(INSTALLER), *args],
            env=self.env,
            capture_output=True,
            text=True,
            stdin=subprocess.DEVNULL,
            timeout=5,
            check=False,
        )

    def assert_installed(
        self, result: subprocess.CompletedProcess[str], directory: Path
    ) -> None:
        self.assertEqual(result.returncode, 0, result.stderr)
        executable = directory / "teamtypev"
        self.assertTrue(executable.is_file())
        self.assertEqual(executable.stat().st_mode & 0o777, 0o755)
        self.assertIn(
            f"Installed teamtypev test-version to {executable}", result.stdout
        )
        self.assertEqual(list(self.root.glob("tmp.*")), [])

    def test_default_directory_release_and_platform_aliases(self) -> None:
        for system, arch, platform in (
            ("Linux", "x86_64", "x86_64-linux-static"),
            ("Linux", "amd64", "x86_64-linux-static"),
            ("Linux", "aarch64", "aarch64-linux-static"),
            ("Linux", "arm64", "aarch64-linux-static"),
            ("Darwin", "x86_64", "universal-apple-darwin"),
            ("Darwin", "arm64", "universal-apple-darwin"),
        ):
            with self.subTest(system=system, arch=arch):
                self.env.update(TEST_OS=system, TEST_ARCH=arch)
                directory = self.root / "home/.local/bin"
                self.assert_installed(self.run_install(), directory)
                self.assertEqual(
                    (self.root / "url").read_text().strip(),
                    f"https://github.com/SichangHe/TeamTypeV/releases/download/nightly/teamtypev-{platform}.tar.gz",
                )

    def test_custom_directory_and_release_preserve_spaces(self) -> None:
        directory = self.root / "custom bin"
        result = self.run_install("--release", "v1.2.3", "--dir", str(directory))
        self.assert_installed(result, directory)
        self.assertIn("/v1.2.3/", (self.root / "url").read_text())
        self.assertIn("is not in your PATH", result.stdout)

    def test_directory_already_in_path_suppresses_note(self) -> None:
        directory = self.root / "installed"
        self.env["PATH"] += os.pathsep + str(directory)
        result = self.run_install("--dir", str(directory))
        self.assert_installed(result, directory)
        self.assertNotIn("is not in your PATH", result.stdout)

    def test_wget_fallback(self) -> None:
        (self.bin / "curl").unlink()
        self.downloader("wget")
        self.assert_installed(self.run_install(), self.root / "home/.local/bin")
        self.assertIn("/nightly/", (self.root / "url").read_text())

    def test_help_exits_before_platform_detection_or_download(self) -> None:
        self.script("uname", "exit 99\n")
        for option in ("-h", "--help"):
            with self.subTest(option=option):
                result = self.run_install(option)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(
                    "Usage: install.sh [--dir DIR] [--release TAG]", result.stdout
                )
                self.assertFalse((self.root / "url").exists())
                self.assertFalse((self.root / "home").exists())

    def test_unknown_option_is_rejected_before_download(self) -> None:
        result = self.run_install("--unknown")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unknown option --unknown", result.stderr)
        self.assertFalse((self.root / "url").exists())

    def test_options_require_values(self) -> None:
        for option in ("--dir", "--release", "--editor"):
            with self.subTest(option=option):
                self.assertNotEqual(self.run_install(option).returncode, 0)
                self.assertFalse((self.root / "url").exists())

    def test_unattended_default_skips_editor_setup(self) -> None:
        result = self.run_install()
        self.assert_installed(result, self.root / "home/.local/bin")
        self.assertNotIn("Set up editors", result.stdout)
        self.assertFalse((self.root / "home/.local/share").exists())

    def test_unknown_editor_is_rejected_before_download(self) -> None:
        result = self.run_install("--editor", "unknown")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unknown editor", result.stderr)
        self.assertFalse((self.root / "url").exists())

    def test_neovim_uses_xdg_data_and_app_name(self) -> None:
        self.env.update(
            XDG_DATA_HOME=str(self.root / "data dir"), NVIM_APPNAME="custom-nvim"
        )
        result = self.run_install("--editor", "nvim", "--release", "custom")
        self.assertEqual(result.returncode, 0, result.stderr)
        plugin = (
            self.root
            / "data dir/custom-nvim/site/pack/plugins/start/teamtypev/plugin/teamtypev.lua"
        )
        self.assertIn("teamtypev_test_loaded", plugin.read_text())
        self.assertIn("/custom/teamtypev-nvim.tar.gz", (self.root / "url").read_text())

    def test_emacs_preserves_init_and_does_not_duplicate_loader(self) -> None:
        home = self.root / 'home with "quotes"'
        home.mkdir()
        self.env["HOME"] = str(home)
        init = home / ".emacs"
        original = ";; Existing user configuration\n(setq inhibit-startup-screen t)\n"
        _ = init.write_text(original)
        directory = home / "bin directory"
        for _ in range(2):
            self.assert_installed(
                self.run_install("--editor", "emacs", "--dir", str(directory)),
                directory,
            )
        self.assertTrue(init.read_text().startswith(original))
        self.assertEqual(init.read_text().count("setup.el"), 1)
        self.assertIn(r"\"quotes\"", init.read_text())
        setup = home / ".local/share/teamtypev/emacs/setup.el"
        self.assertIn("add-to-list 'exec-path", setup.read_text())
        self.assertIn("bin directory", setup.read_text())
        self.assertTrue(setup.with_name("teamtypev.el").exists())

    def test_lazyvim_preserves_custom_spec_and_prints_manual_setup(self) -> None:
        config = self.root / "config/custom-nvim"
        self.env.update(XDG_CONFIG_HOME=str(config.parent), NVIM_APPNAME=config.name)
        (config / "lua/config").mkdir(parents=True)
        _ = (config / "lua/config/lazy.lua").write_text('{ import = "plugins" },\n')
        spec = config / "lua/plugins/teamtypev-installer.lua"
        spec.parent.mkdir()
        original = 'return { { "my/custom-plugin" } }\n'
        _ = spec.write_text(original)
        result = self.run_install("--editor", "nvim")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(spec.read_text(), original)
        self.assertIn("was preserved", result.stdout)
        self.assertIn('name = "teamtypev", lazy = false', result.stdout)

    def test_lazyvim_creates_distinct_eager_spec_and_updates_it_on_rerun(self) -> None:
        config = self.root / 'config with "quotes"/custom-nvim'
        self.env.update(XDG_CONFIG_HOME=str(config.parent), NVIM_APPNAME=config.name)
        (config / "lua/config").mkdir(parents=True)
        _ = (config / "lua/config/lazy.lua").write_text("  { import = 'plugins' },\n")
        upstream = config / "lua/plugins/teamtype.lua"
        upstream.parent.mkdir()
        _ = upstream.write_text('return { "teamtype/teamtype-nvim" }\n')
        for _ in range(2):
            result = self.run_install("--editor", "nvim")
            self.assertEqual(result.returncode, 0, result.stderr)
        spec = (upstream.parent / "teamtypev-installer.lua").read_text()
        self.assertIn('name = "teamtypev", lazy = false', spec)
        self.assertEqual(spec.count("return"), 1)
        self.assertIn("custom-nvim/site/pack/plugins/start/teamtypev", spec)
        self.assertEqual(upstream.read_text(), 'return { "teamtype/teamtype-nvim" }\n')

    def test_real_lazy_nvim_loads_installed_plugin_with_native_packages_disabled(
        self,
    ) -> None:
        lazy_path = os.environ.get("TEAMTYPEV_TEST_LAZY_NVIM")
        nvim = shutil.which("nvim", path=os.environ["PATH"])
        if not lazy_path or not nvim:
            self.skipTest(
                "set TEAMTYPEV_TEST_LAZY_NVIM to a lazy.nvim checkout and install nvim"
            )
        config = self.root / "config/nvim"
        (config / "lua/config").mkdir(parents=True)
        _ = (config / "init.lua").write_text('require("config.lazy")\n')
        _ = (
            config / "lua/config/lazy.lua"
        ).write_text("""vim.opt.rtp:prepend(vim.env.TEAMTYPEV_TEST_LAZY_NVIM)
require("lazy").setup({
  spec = {
    { import = "plugins" },
  },
  install = { missing = false },
  checker = { enabled = false },
  change_detection = { enabled = false },
})
""")
        self.env.update(XDG_CONFIG_HOME=str(config.parent), NVIM_APPNAME="nvim")
        with tarfile.open(self.root / "teamtypev-nvim.tar.gz", "w:gz") as archive:
            archive.add(INSTALLER.parent / "nvim-plugin", arcname=".")
        result = self.run_install("--editor", "nvim")
        self.assertEqual(result.returncode, 0, result.stderr)
        check = self.root / "check.lua"
        _ = check.write_text("""assert(not vim.o.loadplugins)
assert(vim.fn.exists(":TeamtypevInfo") == 2)
assert(package.loaded["teamtypev"])
assert(vim.fn.executable("teamtypev") == 1)
vim.cmd("qa!")
""")
        result = subprocess.run(
            [
                nvim,
                "--headless",
                "-c",
                'lua local ok, err = pcall(dofile, vim.env.TEAMTYPEV_TEST_CHECK); if not ok then print(err); vim.cmd("cquit 1") end',
            ],
            env={
                **self.env,
                "PATH": os.environ["PATH"],
                "TEAMTYPEV_TEST_LAZY_NVIM": lazy_path,
                "TEAMTYPEV_TEST_CHECK": str(check),
                "XDG_DATA_HOME": str(self.root / "home/.local/share"),
                "XDG_STATE_HOME": str(self.root / "state"),
                "XDG_CACHE_HOME": str(self.root / "cache"),
            },
            capture_output=True,
            cwd=self.root,
            text=True,
            timeout=15,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_emacs_xdg_init(self) -> None:
        config = self.root / "config/emacs"
        config.mkdir(parents=True)
        self.env["XDG_CONFIG_HOME"] = str(config.parent)
        result = self.run_install("--editor", "emacs")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("setup.el", (config / "init.el").read_text())

    def test_emacs_prefers_el_to_bare_init(self) -> None:
        home = self.root / "home"
        home.mkdir()
        _ = (home / ".emacs").write_text(";; bare init\n")
        _ = (home / ".emacs.el").write_text(";; source init\n")
        result = self.run_install("--editor", "emacs")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((home / ".emacs").read_text(), ";; bare init\n")
        self.assertIn("setup.el", (home / ".emacs.el").read_text())

    def test_emacs_xdg_takes_precedence_over_el_without_legacy_directory(self) -> None:
        home = self.root / "home"
        config = home / ".config/emacs"
        config.mkdir(parents=True)
        _ = (home / ".emacs.el").write_text(";; unused init\n")
        result = self.run_install("--editor", "emacs")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((home / ".emacs.el").read_text(), ";; unused init\n")
        self.assertIn("setup.el", (config / "init.el").read_text())

    def test_emacs_compiled_init_is_preserved_with_manual_guidance(self) -> None:
        for relative in (".emacs.el", ".emacs.d/init.el"):
            with self.subTest(relative=relative):
                home = self.root / relative.replace("/", "_")
                self.env["HOME"] = str(home)
                init = home / relative
                init.parent.mkdir(parents=True)
                compiled = init.with_suffix(".elc")
                _ = compiled.write_bytes(b"compiled user configuration")
                result = self.run_install("--editor", "emacs")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("automatic init setup was skipped", result.stdout)
                self.assertIn("recompile", result.stdout)
                self.assertIn("setup.el", result.stdout)
                self.assertEqual(compiled.read_bytes(), b"compiled user configuration")
                self.assertFalse(init.exists())

    def test_code_and_codium_install_release_extension(self) -> None:
        for editor in ("code", "codium"):
            with self.subTest(editor=editor):
                self.script(
                    editor,
                    """test "$1" = --install-extension
test "$3" = --force
test -s "$2"
printf '%s\\n' "$0" > "$TEST_ROOT/editor"
""",
                )
                result = self.run_install("--editor", editor)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(
                    (self.root / "editor").read_text().strip(), str(self.bin / editor)
                )
                self.assertIn(
                    "/nightly/teamtypev.vsix", (self.root / "url").read_text()
                )

    def test_missing_code_command_explains_recovery(self) -> None:
        result = self.run_install("--editor", "code")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("rerun with --editor code", result.stderr)
        self.assertTrue((self.root / "home/.local/bin/teamtypev").exists())

    def test_multiple_editors_preserve_upstream_installations(self) -> None:
        home = self.root / "home"
        existing = {
            ".local/bin/teamtype": "upstream binary",
            ".local/share/teamtype/emacs/teamtype.el": "upstream Emacs plugin",
            ".local/share/nvim/site/pack/plugins/start/teamtype/plugin/teamtype.lua": "upstream Neovim plugin",
            ".emacs.d/init.el": '(load "~/.local/share/teamtype/emacs/teamtype.el")\n',
        }
        for relative, content in existing.items():
            path = home / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            _ = path.write_text(content)
        for editor in ("code", "codium"):
            self.script(editor, 'printf "%s\\n" "$0" >> "$TEST_ROOT/editors"\n')
        result = self.run_install(
            "--editor",
            "nvim",
            "--editor",
            "emacs",
            "--editor",
            "code",
            "--editor",
            "codium",
            "--editor",
            "code",
        )
        self.assert_installed(result, home / ".local/bin")
        for relative, content in existing.items():
            self.assertTrue((home / relative).read_text().startswith(content))
        self.assertIn(
            "teamtypev/emacs/setup.el", (home / ".emacs.d/init.el").read_text()
        )
        self.assertTrue(
            (
                home
                / ".local/share/nvim/site/pack/plugins/start/teamtypev/plugin/teamtypev.lua"
            ).exists()
        )
        self.assertEqual(
            (self.root / "editors").read_text().splitlines(),
            [str(self.bin / "code"), str(self.bin / "codium")],
        )
        self.assertNotIn("disable it", result.stdout)

    def test_no_editor_clears_explicit_selections(self) -> None:
        result = self.run_install(
            "--editor", "emacs", "--editor", "nvim", "--no-editor"
        )
        self.assert_installed(result, self.root / "home/.local/bin")
        self.assertFalse((self.root / "home/.local/share").exists())

    def test_piped_script_prompts_on_terminal_and_can_skip(self) -> None:
        for choice, args in (("1 2", []), ("2", []), ("", []), ("", ["--no-editor"])):
            with self.subTest(choice=choice, args=args):
                master, slave = pty.openpty()

                def terminal() -> None:
                    os.setsid()
                    _ = fcntl.ioctl(1, termios.TIOCSCTTY, 0)

                with subprocess.Popen(
                    ["/bin/sh", "-s", "--", *args],
                    stdin=subprocess.PIPE,
                    stdout=slave,
                    stderr=slave,
                    env=self.env,
                    preexec_fn=terminal,
                ) as process:
                    os.close(slave)
                    try:
                        assert process.stdin is not None
                        _ = process.stdin.write(INSTALLER.read_bytes())
                        process.stdin.close()
                        output = b""
                        answered = False
                        deadline = time.monotonic() + 5
                        while time.monotonic() < deadline:
                            ready, _, _ = select.select([master], [], [], 0.1)
                            if ready:
                                try:
                                    chunk = os.read(master, 65536)
                                except OSError:
                                    break
                                if not chunk:
                                    break
                                output += chunk
                                if b"[Enter] Skip:" in output and not answered:
                                    _ = os.write(master, (choice + "\n").encode())
                                    answered = True
                            elif process.poll() is not None:
                                break
                        self.assertEqual(process.wait(timeout=1), 0, output.decode())
                        self.assertEqual(answered, not args)
                        if "2" in choice:
                            self.assertIn(b"Installed Emacs plugin", output)
                        if "1" in choice:
                            self.assertIn(b"Installed Neovim plugin", output)
                    finally:
                        if process.poll() is None:
                            process.kill()
                        os.close(master)

    def test_unsupported_platforms_are_rejected_before_download(self) -> None:
        for system, arch in (("Linux", "riscv64"), ("FreeBSD", "x86_64")):
            with self.subTest(system=system, arch=arch):
                self.env.update(TEST_OS=system, TEST_ARCH=arch)
                result = self.run_install()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(f"no prebuilt binary for {system} {arch}", result.stderr)
                self.assertFalse((self.root / "url").exists())


if __name__ == "__main__":
    _ = unittest.main()
