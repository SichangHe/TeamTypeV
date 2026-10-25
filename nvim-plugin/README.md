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

### Manual installation

Clone TeamTypeV and link its bundled plugin into Neovim's package directory:

```
git clone --branch live-multi-editor https://github.com/SichangHe/TeamTypeV "$HOME/TeamTypeV"
mkdir -p "$HOME/.local/share/nvim/site/pack/plugins/start"
ln -s "$HOME/TeamTypeV/nvim-plugin" "$HOME/.local/share/nvim/site/pack/plugins/start/teamtype"
```

### Plugin managers

Point your plugin manager at the `nvim-plugin` directory in your TeamTypeV checkout. The upstream `teamtype/teamtype-nvim` repository does not contain TeamTypeV's changes.

#### Lazy

```lua
{
  dir = vim.fn.expand("~/TeamTypeV/nvim-plugin"),
  keys = {
    { "<leader>ej", "<cmd>TeamtypeJumpToCursor<cr>" },
    { "<leader>ef", "<cmd>TeamtypeFollow<cr>" },
  },
  lazy = false,
}
```

#### pckr.nvim

```lua
{
  vim.fn.expand("~/TeamTypeV/nvim-plugin"),
  config = function()
    vim.keymap.set("n", "<leader>ej", "<cmd>TeamtypeJumpToCursor<cr>")
    vim.keymap.set("n", "<leader>ef", "<cmd>TeamtypeFollow<cr>")
  end
}
```

## Confirm the installation

To confirm that the plugin is installed, try running the `:TeamtypeInfo` command in Neovim.
It should show the message "Not connected to TeamTypeV daemon."

## Tips

- Create mappings for the `:TeamtypeJumpToCursor` and `:TeamtypeFollow` command, see above configurations for examples.
- Add the output of `require("teamtype").status()` to your status bar, see the [help file](doc/teamtype.txt) for an example.

## Configuration

See the [help file](doc/teamtype.txt) for details on configuring this plugin.
