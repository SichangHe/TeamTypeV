#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Sichang He
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Exercise the installer with local archives and no network access."""
# unittest initializes per-test state in setUp, outside __init__.
# pyright: reportUninitializedInstanceVariable=false, reportImplicitOverride=false

import io
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest


INSTALLER = Path(__file__).resolve().parents[1] / "install.sh"


class InstallTests(unittest.TestCase):
    temp: tempfile.TemporaryDirectory[str]
    root: Path
    bin: Path
    env: dict[str, str]

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="teamtype-install-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        for command in ("tar", "gzip", "mkdir", "mv", "chmod", "mktemp", "rm"):
            executable = shutil.which(command)
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
        payload = b'#!/bin/sh\necho "teamtype test-version"\n'
        with tarfile.open(self.root / "release.tar.gz", "w:gz") as archive:
            member = tarfile.TarInfo("teamtype")
            member.size = len(payload)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(payload))
        self.downloader("curl")

    def script(self, name: str, body: str) -> None:
        path = self.bin / name
        _ = path.write_text("#!/bin/sh\nset -eu\n" + body)
        path.chmod(0o755)

    def downloader(self, name: str) -> None:
        copy = shutil.which("cp")
        assert copy is not None
        if name == "curl":
            body = 'test "$1" = -fsSL\ntest "$3" = -o\nprintf "%s\\n" "$2" > "$TEST_ROOT/url"\n'
            destination = '"$4"'
        else:
            body = 'test "$1" = -qO\nprintf "%s\\n" "$3" > "$TEST_ROOT/url"\n'
            destination = '"$2"'
        self.script(
            name, body + f'"{copy}" "$TEST_ROOT/release.tar.gz" {destination}\n'
        )

    def run_install(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["/bin/sh", str(INSTALLER), *args],
            env=self.env,
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        )

    def assert_installed(
        self, result: subprocess.CompletedProcess[str], directory: Path
    ) -> None:
        self.assertEqual(result.returncode, 0, result.stderr)
        executable = directory / "teamtype"
        self.assertTrue(executable.is_file())
        self.assertEqual(executable.stat().st_mode & 0o777, 0o755)
        self.assertIn(f"Installed teamtype test-version to {executable}", result.stdout)
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
                    f"https://github.com/SichangHe/TeamTypeV/releases/download/nightly/teamtype-{platform}.tar.gz",
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
        for option in ("--dir", "--release"):
            with self.subTest(option=option):
                self.assertNotEqual(self.run_install(option).returncode, 0)
                self.assertFalse((self.root / "url").exists())

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
