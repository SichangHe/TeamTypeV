<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# TeamTypeV
(authored by agents unless marked 🧑)

TeamTypeV provides collaborative editing of local files, editor integration, and Git commands forwarded to the person sharing the directory.

TeamTypeV is independently maintained and derived from [Teamtype](https://github.com/teamtype/teamtype), previously called Ethersync. The original authors built the peer-to-peer collaboration engine, editor protocol, and plugins on which this project depends. Please report TeamTypeV problems [here](https://github.com/SichangHe/TeamTypeV/issues), rather than to the upstream maintainers.

The `teamtype` command, `.teamtype` configuration directory, and editor command identifiers retain their existing names for compatibility. Install TeamTypeV from this repository: packages named `teamtype` in public package managers belong to upstream.

## Installation

Install the latest nightly build into `~/.local/bin` on Linux or macOS. In a terminal, the installer also asks which editor to set up:

```bash
curl -fsSL https://raw.githubusercontent.com/SichangHe/TeamTypeV/live-multi-editor/install.sh | sh
```

To choose directly, replace `sh` with `sh -s -- --editor emacs`, `sh -s -- --editor code` (VS Code), `sh -s -- --editor codium`, or `sh -s -- --editor nvim`. Rerun for another editor. Use `sh -s -- --no-editor` to install only the executable.

Add `--dir DIR` to install elsewhere, or `--release TAG` for another release, after `sh -s --`. Ensure the installation directory is in your `PATH`, then restart your editor.

To build from source, clone this repository, check out `live-multi-editor`, and run `cargo build --locked --release`. The executable is `target/release/teamtype`.

## Share or join

For a first session, follow the [getting-started guide](book/src/getting-started.md), including editor setup.

In the directory to share:

```bash
teamtype share
```

In a separate directory, join using the code printed by the sharer:

```bash
teamtype join CODE
```

Joining replaces local directory contents with the sharer's contents; use an empty directory. Keep backups of important work.

Leave both commands running while editing; they run the collaboration daemons used by the editor plugins.

Use the plugins shipped in this repository: [Neovim](nvim-plugin/README.md), [VS Code/Codium](vscode-plugin/README.md), and [Emacs](emacs-plugin/README.md). Upstream marketplace plugins may lack TeamTypeV's editor changes.

## Git in a shared directory

The sharer keeps the Git repository. Joiners run `teamtype git status`, `teamtype git add FILE`, and `teamtype git commit -m "MESSAGE"`; commands wait for their preceding edits and execute on the sharer. Checkout and other file changes synchronize to everyone. Joiners need no `.git`.

For ordinary `git`, run `source .teamtype/activate` in bash or zsh, or `source .teamtype/activate.fish` in fish, before starting your editor. Run `deactivate` to restore your PATH. Terminal commands support interactive editors, `add -p`, pagers, and colors using the sharer's programs and configuration. Tools that read `.git` directly still need a local repository. Both VCS synchronization flags are deprecated no-ops. See [Git setup and limits](book/src/git-integration-synchronized.md), including automatic activation with direnv.

## Documentation and checks

Read the [user documentation](book/src/introduction.md), [editor protocol](book/src/editor-plugin-dev-guide.md), and [contributing guide](CONTRIBUTING.md).

The repository contains [automated feature checks](verification/feature-tests.md) and tests against real daemons and editors. The name TeamTypeV does not imply that the whole system is formally verified; tests establish only the behaviors they exercise.

## Upstream credit

Credit belongs to [Teamtype's contributors](https://github.com/teamtype/teamtype/graphs/contributors), including Moritz Neeb (zormit), blinry, and Caleb Maclennan. Copyright notices, license files, Git history, and the [upstream changelog](CHANGELOG.md) preserve their contributions. Historical design records describe upstream decisions under the original name.

Upstream Teamtype received funding from [NLnet's NGI0 Core Fund](https://nlnet.nl/core/) in 2024 and the [Prototype Fund](https://www.prototypefund.de/) and [Federal Ministry of Research, Technology and Space](https://www.bmbf.de/EN/) in 2025. These acknowledgments describe upstream funding, not funding awarded to TeamTypeV.

Teamtype's [documentation](https://teamtype.github.io/teamtype/), [FOSDEM 2025 talk](https://fosdem.org/2025/schedule/event/fosdem-2025-4890-ethersync-real-time-collaboration-in-your-text-editor-/), and [community](https://teamtype.zulipchat.com) explain the original project. The implementation builds on [Automerge](https://automerge.org), [Iroh](https://www.iroh.computer), and [Magic Wormhole](https://magic-wormhole.readthedocs.io).

## License

The program is licensed under the GNU Affero General Public License, version 3 or later. Individual files retain their copyright and license notices; see [LICENSE.md](LICENSE.md) and [LICENSES](LICENSES/).
