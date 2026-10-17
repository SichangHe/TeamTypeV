<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Ignored files

Teamtype ignores

- `.teamtype` and everything in it,
- all files ignored via `.teamtypeignore` files (which work like `.gitignore` files),
- everything that Git would [ignore](https://git-scm.com/docs/gitignore), and
- version control directories including `.git`, `.jj`, `.bzr`, `.hg`, `.pijul`, and even `.svn`, and everything in them, if you pass `--no-sync-vcs`.
  By default these directories are shared, see [here](git-integration-synchronized.md) for details.
  Files that Git tracks are then shared even if they are ignored, so that every peer's Git sees the same files.

Note that you shouldn't rely on `.gitignore` or `.teamtypeignore` files to "protect sensitive information" from being shared with peers you don't trust, as the peers could easily delete these ignore files.
