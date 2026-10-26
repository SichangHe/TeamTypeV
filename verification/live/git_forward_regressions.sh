#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Sichang He
# SPDX-License-Identifier: AGPL-3.0-or-later
# Real-daemon regressions. CASE selects one case; defaults to all. Prints only failures.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
TEAMTYPEV_BINARY=${TEAMTYPEV_BINARY:-$root/target/debug/teamtypev}
work=$(mktemp -d "${TMPDIR:-/tmp}/teamtypev-git-regressions.XXXXXX")
pids=()
success=
cleanup() {
    kill "${pids[@]}" 2>/dev/null || true
    wait 2>/dev/null || true
    if [ -n "$success" ]; then rm -rf "$work"; else echo "FAIL: kept $work" >&2; fi
}
trap cleanup EXIT
fail() { echo "FAIL: $*" >&2; exit 1; }
eventually() {
    for _ in $(seq 300); do
        "$@" && return 0
        sleep 0.1
    done
    return 1
}
in_dir() { local dir=$1; shift; (cd "$work/$dir" && "$@"); }
remote() { in_dir b "$TEAMTYPEV_BINARY" git "$@" </dev/null; }
has_text() { [ "$(cat "$work/$1/f.txt" 2>/dev/null)" = "$2" ]; }
start() {
    local dir=$1; shift
    (cd "$work/$dir" && exec "$TEAMTYPEV_BINARY" "$@" </dev/null >>"$work/$dir.log" 2>&1) &
    pids+=("$!")
}
mkdir -p "$work/a/.teamtypev" "$work/b/.teamtypev"
in_dir a git init -qb master
in_dir a git config user.name Test
in_dir a git config user.email test@example.test
printf 'initial\n' >"$work/a/f.txt"
printf 'old\n' >"$work/a/ignored.txt"
printf 'ignored.txt\n' >"$work/a/.gitignore"
in_dir a git add -f f.txt ignored.txt .gitignore
in_dir a git commit -qm initial
if [ "${CASE:-all}" = portable ]; then
    mkdir "$work/bin"
    printf '#!/bin/sh\nexit 99\n' >"$work/bin/setsid"
    chmod +x "$work/bin/setsid"
    export PATH="$work/bin:$PATH"
fi
start a share --no-join-code --show-secret-address
eventually grep -aq 'peer=' "$work/a.log" || fail 'no sharer address'
grep -aoE 'peer=[^ ]+' "$work/a.log" >"$work/b/.teamtypev/config"
start b join
eventually has_text b initial || fail 'no initial sync'
eventually test -f "$work/b/ignored.txt" || fail 'tracked ignored file not shared'
if [[ ${CASE:-all} = open || ${CASE:-all} = all ]]; then
    mkfifo "$work/open-input"
    exec 8<>"$work/open-input"
    timeout 10s bash -c 'cd "$1" && exec "$2" git status --porcelain' _ "$work/b" "$TEAMTYPEV_BINARY" <&8 >"$work/open.out" ||
        fail 'Git status waited for stdin EOF'
    in_dir a git config alias.read-first '!head -c 6'
    printf before >&8
    timeout 10s bash -c 'cd "$1" && exec "$2" git read-first' _ "$work/b" "$TEAMTYPEV_BINARY" <&8 >"$work/first.out" ||
        fail 'Git did not receive stdin before EOF'
    [ "$(cat "$work/first.out")" = before ] || fail 'streamed stdin differs'
    exec 8>&-
fi
if [[ ${CASE:-all} = silent || ${CASE:-all} = all ]]; then
    in_dir a git config alias.silent '!sleep 185'
    timeout 200s bash -c 'cd "$1" && exec "$2" git silent' _ "$work/b" "$TEAMTYPEV_BINARY" </dev/null >"$work/silent.out" 2>"$work/silent.err" ||
        fail 'silent Git command was cancelled'
fi
case ${CASE:-all} in
    portable)
        remote --version >"$work/version" || fail 'Git depends on the setsid utility'
        ;;
    stdin|all)
        { sleep 0.4; printf 'before'; sleep 0.4; printf 'after'; } |
            in_dir b "$TEAMTYPEV_BINARY" git hash-object --stdin >"$work/hash"
        expected=$(printf beforeafter | in_dir a git hash-object --stdin)
        [ "$(cat "$work/hash")" = "$expected" ] || fail 'slow stdin was truncated'
        ;;
esac
if [[ ${CASE:-all} = ignored || ${CASE:-all} = all ]]; then
    printf 'new\n' >"$work/b/ignored.txt"
    remote commit -qam ignored-edit || fail 'tracked ignored edit did not reach commit'
    [ "$(in_dir a git show HEAD:ignored.txt)" = new ] || fail 'commit lost tracked ignored edit'
fi
if [[ ${CASE:-all} = large || ${CASE:-all} = all ]]; then
    dd if=/dev/zero of="$work/input" bs=1048576 count=80 status=none
    in_dir b "$TEAMTYPEV_BINARY" git hash-object --stdin <"$work/input" >"$work/hash" 2>"$work/input.err" &
    upload=$!
    pids+=("$upload")
    printf 'during stdin\n' >"$work/a/f.txt"
    eventually has_text b 'during stdin' || fail 'stdin upload blocked file synchronization'
    wait "$upload" || fail 'large stdin failed'
    expected=$(in_dir a git hash-object --stdin <"$work/input")
    [ "$(cat "$work/hash")" = "$expected" ] || fail 'large stdin differs'
fi
if [[ ${CASE:-all} = queue || ${CASE:-all} = all ]]; then
    dd if=/dev/zero of="$work/input" bs=1048576 count=8 status=none
    blob=$(in_dir a git hash-object -w --stdin <"$work/input")
    mkfifo "$work/stalled"
    exec 9<>"$work/stalled"
    (cd "$work/b" && exec "$TEAMTYPEV_BINARY" git cat-file blob "$blob" </dev/null >&9 2>"$work/stalled.err") &
    stalled=$!
    pids+=("$stalled")
    sleep 2
    (cd "$work/a" && exec "$TEAMTYPEV_BINARY" git status --porcelain </dev/null >"$work/queued.out" 2>"$work/queued.err") &
    queued=$!
    pids+=("$queued")
    eventually grep -q 'queued behind: cat-file' "$work/queued.err" || fail 'waiting client got no queue explanation'
    for _ in $(seq 205); do
        kill -0 "$queued" 2>/dev/null || break
        sleep 1
    done
    kill -0 "$queued" 2>/dev/null && fail 'unconsumed output blocked queue beyond three minutes'
    wait "$queued" || fail 'command after stalled output failed'
    kill "$stalled" 2>/dev/null || true
    wait "$stalled" 2>/dev/null || true
    exec 9>&-
    in_dir a git config alias.progress '!i=0; while [ "$i" -lt 7 ]; do echo live; sleep 30; i=$((i+1)); done'
    remote progress >"$work/progress" || fail 'long command with live output was cancelled'
    [ "$(wc -l <"$work/progress")" -eq 7 ] || fail 'long command output was lost'
fi
success=yes
