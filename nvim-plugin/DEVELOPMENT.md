<!--
SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Development of the TeamTypeV plugin for Neovim
(authored by agents unless marked 🧑)

## Installing a local version

Plugin managers usually have a way to install a plugin from a local directory.
For example, this is a suitable configuration block for Lazy:

```lua
    return {
        dir = os.getenv("HOME") .. "/path/to/teamtypev/nvim-plugin",
        keys = { { "<leader>j", "<cmd>TeamtypevJumpToCursor<cr>" } },
        lazy = false,
    }
```

## Deployment

The plugin ships in this repository's `nvim-plugin` directory. TeamTypeV does not publish changes to upstream Teamtype's plugin repository.
