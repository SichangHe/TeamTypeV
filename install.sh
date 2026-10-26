#!/bin/sh
# SPDX-FileCopyrightText: 2026 Sichang He
#
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# Installs the `teamtype` command from this fork's GitHub releases:
#     curl -fsSL https://raw.githubusercontent.com/SichangHe/TeamTypeV/live-multi-editor/install.sh | sh
# Options, after `sh -s --` when piped:
#     --dir DIR      install into DIR instead of ~/.local/bin
#     --release TAG  install release TAG instead of `nightly`
#     --editor NAME  set up nvim, emacs, code, or codium; `none` skips setup
#     --no-editor    skip the interactive editor menu
set -eu

repo=SichangHe/TeamTypeV
dir="$HOME/.local/bin"
release=nightly
editor=auto
while [ $# -gt 0 ]; do
    case "$1" in
    --dir) dir=$2; shift 2 ;;
    --release) release=$2; shift 2 ;;
    --editor) editor=$2; shift 2 ;;
    --no-editor) editor=none; shift ;;
    -h | --help)
        echo "Usage: install.sh [--dir DIR] [--release TAG] [--editor NAME | --no-editor]"
        echo "Defaults: ~/.local/bin, nightly; editor menu when run in a terminal."
        echo "Editors: nvim, emacs, code (VS Code), codium (VSCodium), none."
        exit 0
        ;;
    *) echo "teamtype install: unknown option $1" >&2; exit 1 ;;
    esac
done
case "$editor" in
auto | none | nvim | emacs | code | codium) ;;
*) echo "teamtype install: unknown editor $editor" >&2; exit 1 ;;
esac

case "$(uname -s)/$(uname -m)" in
Linux/x86_64 | Linux/amd64) platform=x86_64-linux-static ;;
Linux/aarch64 | Linux/arm64) platform=aarch64-linux-static ;;
Darwin/*) platform=universal-apple-darwin ;;
*)
    echo "teamtype install: no prebuilt binary for $(uname -s) $(uname -m)" >&2
    exit 1
    ;;
esac

url="https://github.com/$repo/releases/download/$release/teamtype-$platform.tar.gz"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
download() {
    echo "Downloading $1"
    if command -v curl >/dev/null 2>&1; then
        curl -fsSL "$1" -o "$2"
    else
        wget -qO "$2" "$1"
    fi
}
download "$url" "$work/teamtype.tar.gz"
tar -xzf "$work/teamtype.tar.gz" -C "$work" teamtype
mkdir -p "$dir"
dir=$(cd "$dir" && pwd)
# Replace rather than overwrite, so that a running teamtype keeps its file.
mv -f "$work/teamtype" "$dir/teamtype"
chmod 755 "$dir/teamtype"
echo "Installed $("$dir/teamtype" --version) to $dir/teamtype"

case ":$PATH:" in
*":$dir:"*) ;;
*) echo "Note: $dir is not in your PATH; add it, for example: export PATH=\"$dir:\$PATH\"" ;;
esac

# 🧑 "Maybe the installation script not only installs the binary, but also interactively give editor setup"
if [ "$editor" = auto ]; then
    editor=none
    if [ -t 1 ] && ( : </dev/tty ) 2>/dev/null; then
        exec 3<>/dev/tty
        printf '\nSet up an editor? [1] Neovim [2] Emacs [3] VS Code [4] VSCodium [Enter] Skip: ' >&3
        read -r choice <&3 || choice=
        case "$choice" in
        1 | nvim) editor=nvim ;;
        2 | emacs) editor=emacs ;;
        3 | code) editor=code ;;
        4 | codium) editor=codium ;;
        "") ;;
        *) echo "No editor selected. Rerun with --editor NAME to set one up." ;;
        esac
        exec 3>&-
    fi
fi

assets="https://github.com/$repo/releases/download/$release"
case "$editor" in
nvim)
    plugin="${XDG_DATA_HOME:-$HOME/.local/share}/${NVIM_APPNAME:-nvim}/site/pack/plugins/start/teamtype"
    download "$assets/teamtype-nvim.tar.gz" "$work/nvim.tar.gz"
    mkdir -p "$plugin"
    tar -xzf "$work/nvim.tar.gz" -C "$plugin"
    escaped_dir=$(printf '%s' "$dir" | sed 's/\\/\\\\/g; s/"/\\"/g')
    printf 'vim.env.PATH = "%s:" .. (vim.env.PATH or "")\n' "$escaped_dir" >"$plugin/plugin/00-teamtype-path.lua"
    echo "Installed Neovim plugin to $plugin. Restart Neovim and run :TeamtypeInfo."
    ;;
emacs)
    plugin="$HOME/.local/share/teamtype/emacs"
    download "$assets/teamtype.el" "$work/teamtype.el"
    mkdir -p "$plugin"
    mv -f "$work/teamtype.el" "$plugin/teamtype.el"
    init="$HOME/.emacs.d/init.el"
    if [ ! -e "$HOME/.emacs" ] && [ ! -e "$HOME/.emacs.d" ] && [ -d "${XDG_CONFIG_HOME:-$HOME/.config}/emacs" ]; then
        init="${XDG_CONFIG_HOME:-$HOME/.config}/emacs/init.el"
    elif [ -f "$HOME/.emacs.el" ] || [ -f "$HOME/.emacs.elc" ]; then
        init="$HOME/.emacs.el"
    elif [ -f "$HOME/.emacs" ]; then
        init="$HOME/.emacs"
    fi
    mkdir -p "$(dirname "$init")"
    escaped_plugin=$(printf '%s' "$plugin" | sed 's/\\/\\\\/g; s/"/\\"/g')
    escaped_dir=$(printf '%s' "$dir" | sed 's/\\/\\\\/g; s/"/\\"/g')
    printf '(add-to-list '\''exec-path "%s")\n(load "%s/teamtype.el")\n' "$escaped_dir" "$escaped_plugin" >"$plugin/setup.el"
    loader="(load \"$escaped_plugin/setup.el\")"
    if [ -f "${init}c" ]; then
        echo "Installed Emacs plugin, but automatic init setup was skipped: ${init}c is compiled."
        echo "Add this to its source configuration and recompile it, then restart Emacs:"
        printf '%s\n' "$loader"
    else
        if ! grep -Fqx "$loader" "$init" 2>/dev/null; then
            printf '\n%s\n' "$loader" >>"$init"
        fi
        echo "Installed Emacs plugin and added its loader to $init. Restart Emacs."
    fi
    ;;
code | codium)
    if ! command -v "$editor" >/dev/null 2>&1; then
        echo "teamtype install: $editor command not found; enable the editor's shell command, then rerun with --editor $editor" >&2
        exit 1
    fi
    download "$assets/teamtype.vsix" "$work/teamtype.vsix"
    "$editor" --install-extension "$work/teamtype.vsix" --force
    echo "Installed TeamTypeV for $editor. Restart the editor."
    echo "If the upstream TeamType extension is installed, disable it to avoid duplicate handlers."
    echo "The editor must find $dir/teamtype: launch it from a terminal with that directory in PATH."
    ;;
esac
echo "In a project directory, run: teamtype share"
echo "On another machine, run the teamtype join command printed by the sharer."
echo "Then open files in that directory with your configured editor."
