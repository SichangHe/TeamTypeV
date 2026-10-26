<!--
SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# TeamTypeV Emacs plugin
(authored by agents unless marked 🧑)

## Install

Install the executable and Emacs plugin together:

```bash
curl -fsSL https://raw.githubusercontent.com/SichangHe/TeamTypeV/live-multi-editor/install.sh | sh -s -- --editor emacs
```

The installer adds a loader to your Emacs init file, configures Emacs to find the executable, and prints the init file's location. Restart Emacs.

For a checkout-based installation instead, install the [TeamTypeV executable](../README.md#installation), then add this to your init file, replacing the checkout path:

```emacs-lisp
(add-to-list 'load-path "~/path/to/teamtypev/emacs-plugin")
(require 'teamtypev)
```

Restart Emacs, or evaluate those two forms. For a one-time trial, run `emacs -Q -L emacs-plugin -l teamtypev` from the repository root instead.

Check `M-: (executable-find "teamtypev")`. It must return the installed executable. With manual setup, if a desktop-launched Emacs cannot find it, add the installation directory to `exec-path` in your init file; for the default installer location:

```emacs-lisp
(add-to-list 'exec-path (expand-file-name "~/.local/bin"))
```

## Start editing

Run [`teamtypev share` or `teamtypev join CODE`](../README.md#share-or-join) in a terminal and leave it running. In Emacs, use `C-x C-f` to open a UTF-8 text file in that directory. The plugin connects automatically; there is no mode to enable. If the file was already open before loading the plugin or starting the daemon, close its buffer and reopen it.

Look for `TeamTypeV: tracking` followed by the filename in `*Messages*`. Type in the same file from another connected editor to check that edits appear in both without saving. `C-x C-s` asks the daemon to save. If the daemon stops, shared buffers become read-only; restart it, close those buffers, and reopen the files.

## Automated test

To test against live daemons and a Neovim typing at the same time (needs `docker`, `nvim`, and a built `teamtypev`):

```bash
emacs-plugin/test.sh target/release/teamtypev
```

Run this from the repository root. The test uses Emacs 29 in Docker.

See [implementation design](DESIGN.md) for connection and synchronization behavior.
