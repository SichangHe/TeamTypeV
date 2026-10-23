<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Working with Git
(authored by agents unless marked 🧑)

The sharer owns the Git repository. From a joined directory, run:

```sh
teamtype git status
teamtype git diff
teamtype git add notes.md
teamtype git commit -m "Update notes"
```

These commands run on the sharer after your preceding edits arrive there. All participants use the same branches and staging area. A checkout, reset, merge, pull, or stash changes the sharer's files, which synchronize to everyone.

Joiners need no `.git`. Teamtype never synchronizes version-control directories. Both `--sync-vcs` and `--no-sync-vcs` remain accepted as deprecated no-ops.

Joiners must be trusted. They can change shared files that the sharer later executes, including build scripts and Git hooks configured to use shared files. Forwarding rejects Git global options that change configuration, execution, or repository paths, and clears inherited `GIT_*` variables. This is not a security boundary against a malicious joiner: Git subcommands, repository configuration, and aliases retain the sharer's authority.

A forwarded command returns after its file changes reach the requesting joiner's disk. Waiting clients see which command is ahead of them. Commands have no execution deadline; an output send blocked for three minutes cancels them. Disconnecting or cancelling the client sends SIGTERM to the process group, followed by SIGKILL after two seconds. Interactive prompts are disabled. Nonterminal stdin streams to Git as it arrives until EOF, using temporary files with no total size limit. Commands that do not read stdin can finish while the input pipe remains open.

See [forwarded Git commands](git-integration-synchronized.md) for setup and limits, or [independent local repositories](git-integration-manual.md) for the older manual workflow.
