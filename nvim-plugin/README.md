<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Neovim plugin for 🍃 [TeamTypeV](https://github.com/SichangHe/TeamTypeV)-compatible collaborative software
(authored by agents unless marked 🧑)

This plugin adds real-time collaborative editing functionality to Neovim.
You can use it for pair programming or note-taking, for example.
It is mainly meant to be used with TeamTypeV, but can also be configured to work with other collaborative software speaking the same protocol.

> [!IMPORTANT]
>
> This plugin requires at least Neovim 0.7.0 (which was released in 2022).

## Installation

Install the executable and plugin together, then restart Neovim:

```bash
curl -fsSL https://raw.githubusercontent.com/SichangHe/TeamTypeV/live-multi-editor/install.sh | sh -s -- --editor nvim
```

### Manual installation

Clone TeamTypeV and link its bundled plugin into Neovim's package directory:

```
git clone --branch live-multi-editor https://github.com/SichangHe/TeamTypeV "$HOME/TeamTypeV"
mkdir -p "$HOME/.local/share/nvim/site/pack/plugins/start"
ln -s "$HOME/TeamTypeV/nvim-plugin" "$HOME/.local/share/nvim/site/pack/plugins/start/teamtypev"
```

### Plugin managers

Point your plugin manager at the `nvim-plugin` directory in your TeamTypeV checkout. The upstream `teamtype/teamtype-nvim` repository does not contain TeamTypeV's changes.

#### Lazy

Lazy.nvim disables Neovim's automatic package loading. For a standard LazyVim
configuration importing `plugins` from `lua/config/lazy.lua`, the installer adds
an eager local spec in `lua/plugins/teamtypev-installer.lua` and keeps existing
upstream specs. For manual setup, save this as `lua/plugins/teamtypev.lua`:

```lua
return {
  {
    name = "teamtypev",
    dir = vim.fn.stdpath("data") .. "/site/pack/plugins/start/teamtypev",
    keys = {
      { "<leader>ej", "<cmd>TeamtypevJumpToCursor<cr>" },
      { "<leader>ef", "<cmd>TeamtypevFollow<cr>" },
    },
    lazy = false,
  },
}
```

For another Lazy.nvim setup, add the inner table to your plugin specs. For a
checkout-based installation, replace `dir` with your checkout's `nvim-plugin`
directory. Keep any upstream TeamType spec for `.teamtype` projects; TeamTypeV
uses its own modules, commands, and `.teamtypev` roots.

#### pckr.nvim

```lua
{
  vim.fn.expand("~/TeamTypeV/nvim-plugin"),
  config = function()
    vim.keymap.set("n", "<leader>ej", "<cmd>TeamtypevJumpToCursor<cr>")
    vim.keymap.set("n", "<leader>ef", "<cmd>TeamtypevFollow<cr>")
  end
}
```

## Confirm the installation

To confirm that the plugin is installed, try running the `:TeamtypevInfo` command in Neovim.
Without an active session, it should show "Not connected to any TeamTypeV daemon."

## Tips

- Create mappings for the `:TeamtypevJumpToCursor` and `:TeamtypevFollow` command, see above configurations for examples.
- Add the output of `require("teamtypev").status()` to your status bar, see the [help file](doc/teamtypev.txt) for an example.

## Configuration

See the [help file](doc/teamtypev.txt) for details on configuring this plugin.
