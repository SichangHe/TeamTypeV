<!--
SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Forwarded Git commands
(authored by agents unless marked 🧑)

Run `teamtype share` in the repository. Join from an empty directory, then use `teamtype git ARGS...` there. Commands run in the corresponding directory on the sharer, including when invoked from a subdirectory. Use `teamtype --directory /path/to/shared git ...` from elsewhere to run at the shared root.

Teamtype installs a wrapper at `.teamtype/bin/git` on each joiner. To make ordinary `git` commands and editor Git integrations use forwarding, add its absolute directory to PATH before starting the editor:

```sh
export PATH="$PWD/.teamtype/bin:$PATH"
git status
git commit -am "Update shared files"
```

The wrapper finds the shared root from the current directory. Outside the shared directory, remove this PATH entry to use your ordinary Git. A preexisting joiner's `.git` is left untouched; direct Git without the wrapper still uses that local repository.

The sharer runs forwarded commands one at a time. Each command waits until that joiner's earlier edits have reached the sharer's document and files. Changes must have been sent by the editor plugin; before Git runs, the sharer flushes open buffers to disk, including files normally saved by an editor. Close affected editor buffers before commands that change working files: handling outside changes to open buffers requires a separate editor fix. Changes made by other participants can also be included. Staging is shared: coordinate `add` and `commit` if several people are preparing commits.

Git commands run directly on the sharer use Git's own locks and can conflict with forwarded commands. Use `teamtype git` there as well when you want commands queued together.

Forwarded commands require the shared root to own a non-bare Git repository. A repository in a parent directory is rejected.

## Input and output

Arguments and stdin are forwarded without shell expansion on the sharer. Stdout and stderr stream back as bytes, with Git's exit code (128 plus the signal number when Git is killed). Nonterminal stdin transfers in 16 KiB chunks until EOF and is stored in temporary files before execution. Terminal stdin is empty. Stdin has no total size limit; it needs enough temporary disk space on both peers. Acknowledgements bound input transfers so file synchronization continues during uploads. Output streams through bounded buffers without a total size limit; a slow consumer applies backpressure while file synchronization continues. Three minutes without output progress or consumption cancels the command, and waiting clients see the command ahead of them.

Forwarding is not a sandbox: joiners must be trusted with the sharer's account. Subcommands can access paths outside the shared directory, credentials, configuration, hooks, and aliases. Repository discovery stops at the shared root, but this does not restrict what a Git subcommand can do.

Compared with plain Git, forwarded Git sees pipes rather than a terminal: automatic decorations, progress, columns, and colors may differ. The pager and automatic colors are disabled. Global configuration and repository override options are rejected with exit code 129. Inherited `GIT_*` variables are cleared, SSH uses `ssh -o BatchMode=yes` (overriding `core.sshCommand`), and editor and credential prompts are disabled. Commands use the sharer's identity and configuration, run serially, and wait for file synchronization; failed synchronization barriers return an error even if Git already ran.

Interactive terminal sessions are unsupported. Use `commit -m` or `commit -F -` with piped input. Git editors are disabled, so commits that need an editor and `rebase -i` fail. `add -p` has no terminal interaction; supply its answers through stdin or use ordinary `add`. Hooks, aliases, signing tools, and credential helpers run on the sharer and may have their own interaction requirements.

Push and pull use the sharer's remotes and credentials. Git and SSH terminal credential prompts are disabled; configure credentials on the sharer first. See [Working with Git](git-integration.md) for the trust requirement and rejected global options. Git starts in a separate process group using the operating system's process API on Linux and macOS.

## Disconnection and upgrades

A missing daemon or disconnected sharer returns an error. An unanswered request or sync barrier fails after ten seconds. Running commands have no execution deadline. Client disconnection sends SIGTERM to the command's process group, allowing two seconds for cleanup before SIGKILL. A command returns only after its file changes reach the requesting joiner's disk. If the connection drops after submission, a command may already have run; inspect `status` and `log` before retrying. Teamtype never automatically retries a Git command.

Use the same Teamtype build on all peers; the peer protocol changed. On startup and before forwarded commands, Teamtype removes old Git hooks containing `Installed by teamtype`, including hooks found through `core.hooksPath`. Startup also removes old synchronized metadata from its persisted document. Other hooks are preserved. Version-control directories such as `.git` and `.jj` are always excluded from synchronization. A joiner's leftover Git index is not used for file enumeration. The old Git lock is gone. Both VCS synchronization flags are deprecated no-ops.
