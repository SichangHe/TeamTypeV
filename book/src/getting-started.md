<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Getting started
(authored by agents unless marked 🧑)

1. [Run the installer](https://github.com/SichangHe/TeamTypeV#installation) on each participant's machine and choose your editors when prompted. It installs the executable and matching plugins. You can also select editors with repeated options, such as `--editor emacs --editor code`; `codium` and `nvim` are supported too.
2. Restart your editor. For manual setup or troubleshooting, see [Emacs](https://github.com/SichangHe/TeamTypeV/blob/live-multi-editor/emacs-plugin/README.md), [VS Code/Codium](https://github.com/SichangHe/TeamTypeV/blob/live-multi-editor/vscode-plugin/README.md), or [Neovim](https://github.com/SichangHe/TeamTypeV/blob/live-multi-editor/nvim-plugin/README.md). Use the plugins from this fork.
3. In the directory you want to share, run `teamtypev share` and give the printed join code to your collaborator. Leave the command running.
4. Your collaborator creates an empty directory and runs `teamtypev join CODE` there. Leave that command running too; joining replaces local contents with the sharer's files.
5. Each person opens a text file from their own shared directory in their configured editor. The plugins connect automatically through `.teamtypev`; no editor command is needed to start sharing. If the file was already open before setup, close and reopen it.

Try typing in the same file from both editors. Both should show the edits without saving. You can mix editor types, or try two local directories and editors on one machine. Keep backups of important work.

The terminal commands run the collaboration daemons. Keep them running while editing; the editor plugins connect to them but do not start them. See [Git setup](git-integration-synchronized.md) to use Git from a joining directory.
