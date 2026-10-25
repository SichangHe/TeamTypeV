<!--
SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Forwarded Git commands
(authored by agents unless marked 🧑)

Run `teamtype share` in the repository. Join from an empty directory, then use `teamtype git ARGS...` there. Commands run in the corresponding directory on the sharer, including when invoked from a subdirectory. Use `teamtype --directory /path/to/shared git ...` from elsewhere to run at the shared root.

Joining creates `.teamtype/activate` and `.teamtype/activate.fish`. Activate before starting an editor or another tool that runs Git:

```sh
source .teamtype/activate       # bash or zsh
git status
git add -p
git commit
deactivate
```

In fish, use `source .teamtype/activate.fish`. Activation puts `.teamtype/bin/git` first on PATH; programs launched from that shell inherit it. Repeated activation is safe. `deactivate` restores the previous PATH and any previous `deactivate` function. Restart applications that were already running. Activation files contain an absolute path; restart the joiner after moving its directory.

For automatic activation with direnv, create `.envrc` on the joiner containing:

```sh
source .teamtype/activate
```

Run `direnv allow`. Direnv evaluates this in bash and exports the changed PATH to bash, zsh, or fish. It restores the environment on leaving the directory; shell functions such as `deactivate` are not exported.

The wrapper finds the shared root from the current directory. It applies throughout the activated shell; outside the shared directory, run `deactivate` to use ordinary Git. A preexisting joiner's `.git` is left untouched; Git without the wrapper still uses that local repository. Tools that read `.git` directly, including libgit2-based integrations, cannot treat the joiner's files as a local repository. Tools that invoke the Git executable can use forwarding through the inherited PATH.

The sharer runs forwarded commands one at a time. Each command waits until that joiner's earlier edits have reached the sharer's document and files. Changes must have been sent by the editor plugin; before Git runs, the sharer flushes open buffers to disk. You can keep typing while Git runs. The daemon collects those edits and merges them with Git's completed changes before writing files again. On the sharer, saving or opening a file that does not exist yet reports a retry message during the command; retry after Git finishes. Existing files can still be opened. Changes made by other participants can also be included. Staging is shared: coordinate `add` and `commit` if several people are preparing commits.

Use `teamtype git` on the sharer too: ordinary Git bypasses this coordination. Other programs that keep a shared file open for writing can lose later writes if the daemon replaces that file. Use the editor plugins or the `teamtype agent edit` command for concurrent edits; stop sharing before running an uncoordinated writer that must keep its file open.

Forwarded commands require the shared root to own a non-bare Git repository. A repository in a parent directory is rejected.

## Input and output

Arguments and stdin are forwarded without shell expansion on the sharer. With both stdin and stdout attached to terminals, Git gets a pseudo-terminal on the sharer. Commit editors, `add -p`, `rebase -i`, pagers, automatic colors, and terminal prompts use it. The client's terminal type, input, window changes, and interrupt, quit, termination, and hangup signals are forwarded. Terminal output combines stdout and stderr, and local terminal modes are restored when the client returns. Editors and pagers must be installed on the sharer and use its configuration; local `GIT_EDITOR` and `GIT_PAGER` settings are not forwarded.

With redirected stdin or stdout, Git uses the existing noninteractive pipe path. Stdout and stderr remain separate. Git returns its exit code (128 plus the signal number when killed). Nonterminal stdin transfers as it arrives in 16 KiB chunks until EOF, using private temporary files on both peers. If stdin alone is a terminal, it is empty. Stdin has no total size limit and needs enough temporary disk space. Acknowledgements bound input transfers so file synchronization continues during uploads. Output streams through bounded buffers without a total size limit; a slow consumer applies backpressure while file synchronization continues. An output send blocked for three minutes cancels the command; silent execution has no deadline. Waiting clients see the command ahead of them.

Forwarding is not a sandbox: joiners must be trusted with the sharer's account. Subcommands can access paths outside the shared directory, credentials, configuration, hooks, and aliases. Repository discovery stops at the shared root, but this does not restrict what a Git subcommand can do.

Global configuration and repository override options are rejected with exit code 129. Inherited `GIT_*` variables are cleared. In the noninteractive path, pagers, automatic colors, editors, and credential prompts remain disabled, and SSH uses `ssh -o BatchMode=yes` (overriding `core.sshCommand`). Use `commit -m` or `commit -F -` with piped input in that path. Hooks, aliases, signing tools, and credential helpers run on the sharer and may have their own interaction requirements.

Push and pull use the sharer's remotes and credentials. See [Working with Git](git-integration.md) for the trust requirement and rejected global options. Git starts in a separate process group on Linux and macOS; interactive Git also has its own session and controlling terminal.

## Disconnection and upgrades

A missing daemon or disconnected sharer returns an error. An unanswered request or initial sync barrier fails after ten seconds. Running commands have no execution deadline. Client disconnection sends SIGTERM to the command's process group, allowing two seconds for cleanup before SIGKILL. After Git finishes, a file synchronization delay longer than ten seconds produces a warning and preserves Git's exit code; local files may still be catching up. If the connection drops after submission, a command may already have run; inspect `status` and `log` before retrying. TeamTypeV never automatically retries a Git command.

Use the same TeamTypeV build on all peers; the peer protocol changed. On startup and before forwarded commands, TeamTypeV removes old Git hooks containing `Installed by teamtype`, including hooks found through `core.hooksPath`. Startup also removes old synchronized metadata from its persisted document. Other hooks are preserved. Version-control directories such as `.git` and `.jj` are always excluded from synchronization. A joiner's leftover Git index is not used for file enumeration. The old Git lock is gone. Both VCS synchronization flags are deprecated no-ops.
