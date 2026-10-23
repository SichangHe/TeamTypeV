#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Run the release creation step against a local release-state simulation."""

from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


class NightlyTests(unittest.TestCase):
    def test_rerun_after_partial_upload_reuses_build_release(self) -> None:
        workflow = (
            Path(__file__).resolve().parents[1] / ".github/workflows/nightly.yml"
        ).read_text()
        creation = textwrap.dedent(
            workflow.split("        run: |\n", 1)[1].split("\n  upload-assets:", 1)[0]
        )
        with tempfile.TemporaryDirectory(prefix="teamtype-nightly-") as directory:
            simulation = r"""
                set -eu
                export GITHUB_RUN_ID=123 GITHUB_SHA=abcdef
                gh() {
                    test "$1" = release
                    test "$3" = build-123
                    case "$2" in
                        view) test -f release ;;
                        create)
                            test ! -f release || return 1
                            touch release
                            echo created >> creations
                            ;;
                        *) return 2 ;;
                    esac
                }
            """
            script = textwrap.dedent(simulation) + creation
            for _ in range(2):
                result = subprocess.run(
                    ["bash", "-c", script],
                    cwd=directory,
                    capture_output=True,
                    text=True,
                    timeout=5,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(
                (Path(directory) / "creations").read_text(), "created\n"
            )


if __name__ == "__main__":
    unittest.main()
