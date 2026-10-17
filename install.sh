#!/bin/sh
# SPDX-FileCopyrightText: 2026 Sichang He
#
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# Installs the `teamtype` command from this fork's GitHub releases:
#     curl -fsSL https://raw.githubusercontent.com/SichangHe/teamtype--teamtype/live-multi-editor/install.sh | sh
# Options, after `sh -s --` when piped:
#     --dir DIR      install into DIR instead of ~/.local/bin
#     --release TAG  install release TAG instead of `nightly`
set -eu

repo=SichangHe/teamtype--teamtype
dir="$HOME/.local/bin"
release=nightly
while [ $# -gt 0 ]; do
    case "$1" in
    --dir) dir=$2; shift 2 ;;
    --release) release=$2; shift 2 ;;
    -h | --help)
        echo "Usage: install.sh [--dir DIR] [--release TAG]  (defaults: ~/.local/bin, nightly)"
        exit 0
        ;;
    *) echo "teamtype install: unknown option $1" >&2; exit 1 ;;
    esac
done

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
echo "Downloading $url"
if command -v curl >/dev/null 2>&1; then
    curl -fsSL "$url" -o "$work/teamtype.tar.gz"
else
    wget -qO "$work/teamtype.tar.gz" "$url"
fi
tar -xzf "$work/teamtype.tar.gz" -C "$work" teamtype
mkdir -p "$dir"
# Replace rather than overwrite, so that a running teamtype keeps its file.
mv -f "$work/teamtype" "$dir/teamtype"
chmod 755 "$dir/teamtype"
echo "Installed $("$dir/teamtype" --version) to $dir/teamtype"

case ":$PATH:" in
*":$dir:"*) ;;
*) echo "Note: $dir is not in your PATH; add it, for example: export PATH=\"$dir:\$PATH\"" ;;
esac
