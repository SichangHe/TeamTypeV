# installer tests
(authored by agents unless marked 🧑)

- run `python3 verification/test_install.py`
- runs the real installer in a temporary directory
  - replaces `uname` to cover supported and unsupported platforms
  - replaces curl/wget with local archive copies; no network access
  - uses real archive extraction, file replacement, permissions, and version execution
- checks default/custom options, aliases, help, invalid arguments, download fallback, PATH notices, and temporary directory cleanup
- editor setup
  - repeat `--editor nvim|emacs|code|codium` to install multiple editors; `--no-editor` clears selections and skips setup
  - terminal menu accepts space-separated choices from `/dev/tty`, preserving piped script input; unattended runs skip it
  - binary, release assets, and plugin installation directories use `teamtypev`, preserving upstream TeamType installations
  - Neovim uses its standard package directory, respecting `XDG_DATA_HOME` and `NVIM_APPNAME`; startup adds the binary directory to PATH
    - standard LazyVim `lua/config/lazy.lua` importing `plugins` gets a separate eager local spec at `lua/plugins/teamtypev-installer.lua`
    - existing custom specs are preserved; other plugin managers receive the local spec for manual setup
  - Emacs keeps existing configuration and appends one loader; generated setup adds the binary directory to `exec-path`
    - follows Emacs's legacy/XDG init selection; compiled init files receive manual loader/recompilation guidance without configuration changes
  - Code/Codium uses the editor CLI to install a packaged VSIX; its process still needs the binary directory in PATH
- tests exercise local editor assets and a real pseudoterminal with piped script input
  - check configuration preservation, repeat installation, XDG paths, quoted paths, missing editor commands, and explicit skip
  - editor command substitutes check CLI arguments; real editor startup requires separate smoke tests
- run with `TEAMTYPEV_TEST_LAZY_NVIM=/path/to/lazy.nvim python3 verification/test_install.py` to verify real lazy.nvim loads the installed plugin with native package loading disabled
  - uses an isolated configuration and disables missing-plugin installation; does not update existing plugins
- requires Python 3 and the installer's standard Unix tools
