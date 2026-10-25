<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Ignored files
(authored by agents unless marked 🧑)

TeamTypeV ignores

- `.teamtype` and everything in it,
- all files ignored via `.teamtypeignore` files (which work like `.gitignore` files),
- everything that Git would [ignore](https://git-scm.com/docs/gitignore), and
- version-control directories including `.git`, `.jj`, `.bzr`, `.hg`, `.pijul`, and `.svn`, and everything in them.

Git-tracked working files are shared even when an ignore pattern matches them. Git commands from joiners [run on the sharer](git-integration-synchronized.md). The old VCS synchronization flags are deprecated no-ops.

Note that you shouldn't rely on `.gitignore` or `.teamtypeignore` files to "protect sensitive information" from being shared with peers you don't trust, as the peers could easily delete these ignore files.
