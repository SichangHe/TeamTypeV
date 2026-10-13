<!--
SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

To install, add this to your `~/.config/emacs/init.el` (or `~/.emacs`):

```emacs-lisp
(add-to-list 'load-path "~/path/to/teamtype/emacs-plugin")
(require 'teamtype)
```

To test against live daemons and a Neovim typing at the same time (needs `docker`, `nvim`, and a built `teamtype`):

```bash
emacs-plugin/test.sh
```
