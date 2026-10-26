<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# VS Code plugin for 🍃 [TeamTypeV](https://github.com/SichangHe/TeamTypeV)-compatible projects
(authored by agents unless marked 🧑)

Install the [TeamTypeV executable](../README.md#installation) and this extension. VS Code 1.89 or newer is required.

## Install

Install the executable and extension together:

```bash
curl -fsSL https://raw.githubusercontent.com/SichangHe/TeamTypeV/live-multi-editor/install.sh | sh -s -- --editor code
```

For VSCodium, use `--editor codium`. The editor's `code` or `codium` shell command must be available. Restart the editor after installation.

To install a downloaded `teamtypev.vsix` manually, run **Extensions: Install from VSIX...** from the Command Palette and select the file, or run `code --install-extension teamtypev.vsix`. For VSCodium, use `codium` instead of `code`.

To build a package from this checkout, run these commands in `vscode-plugin` (requires Node.js and npm):

```bash
npm ci
npx --yes @vscode/vsce package --out teamtypev.vsix
code --install-extension teamtypev.vsix
```

For extension development, use the [development setup](DEVELOPMENT.md#how-to-run-locally). The upstream marketplace extension does not contain TeamTypeV's changes.

The extension ID is `SichangHe.teamtypev`. It uses separate `teamtypev.*` settings and commands and detects `.teamtypev` directories, so upstream TeamType can remain installed.

## Start editing

Run [`teamtypev share` or `teamtypev join CODE`](../README.md#share-or-join) in a terminal and leave it running. Open that directory with `code .`, then open a text file. The extension finds `.teamtypev` and connects automatically. It replaces the ordinary file tab with a shared tab; edit there. Edits appear in other connected editors without saving, and Save asks the daemon to save the file.

If the file was already open before starting the daemon, close it and reopen it. After changing extension settings, run **Developer: Reload Window**.

If the extension reports that `teamtypev` is not in your `PATH`, fully quit VS Code and start it from a terminal where `teamtypev --version` works. Alternatively, set `cmd` below to the full executable path followed by `"client"`. In SSH, WSL, or container windows, install both the extension and executable in that remote environment, where the shared directory and daemon run.

## Configuration

A configuration for connecting to TeamTypeV daemons is provided as a default value.

You can also use this plugin with other collaboration servers.

To add other configurations, add a section like this to your `settings.json` (you can access it using *F1 -> Preferences: Open User Settings (JSON)*):

```jsonc
"teamtypev.configs": {
  /* Default configuration */
  "teamtypev": {
    "cmd": [ "teamtypev", "client" ],
    "rootMarkers": [ ".teamtypev" ]
   },

  /* Hypothetical configuration for another program */
  "http": {
    "cmd": [ "teamtypev-http" ],
    "rootMarkers": [ ".teamtypev-http" ]
  },
}
```

Available options:

- `cmd`: Array of strings to specify the command to be launched to connect to the collaboration server.
- `rootMarkers`: Array of strings to indicate if a directory should be considered as a collaboration project for this configuration.
