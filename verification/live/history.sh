#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Sichang He
#
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# Live trial: a joiner whose history differs from the sharer's refuses to merge, and joining again
# takes the sharer's files. Also checks that a restarted sharer keeps its history.
# Needs a built `teamtype` (`cargo build -p teamtype`).
# Prints only failures; exit status 0 means every check passed.
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
TEAMTYPE_BINARY=${TEAMTYPE_BINARY:-$root/target/debug/teamtype}
work=$(mktemp -d "${TMPDIR:-/tmp}/teamtype-history.XXXXXX")
pids=()
n_failures=0
cleanup() {
    kill "${pids[@]}" 2>/dev/null
    wait 2>/dev/null
    [ "$n_failures" -eq 0 ] && rm -rf "$work" || echo "kept $work" >&2
}
trap cleanup EXIT
fail() {
    echo "FAIL: $*" >&2
    n_failures=$((n_failures + 1))
}
eventually() {
    for _ in $(seq 300); do
        "$@" && return 0
        sleep 0.2
    done
    return 1
}
start() {
    local dir=$1
    shift
    (cd "$work/$dir" && exec "$TEAMTYPE_BINARY" "$@" </dev/null >>"$work/$dir.log" 2>&1) &
    last_pid=$!
    pids+=("$last_pid")
}
stop() { kill "$1" && wait "$1" 2>/dev/null; }
b_has() { [ "$(cat "$work/b/f.txt" 2>/dev/null)" = "$1" ]; }

mkdir -p "$work/a/.teamtype" "$work/b/.teamtype"
echo one >"$work/a/f.txt"
start a share --no-join-code --show-secret-address
sharer=$last_pid
eventually grep -aq 'peer=' "$work/a.log" || {
    fail "sharing daemon printed no secret address"
    exit 1
}
grep -aoE 'peer=[^ ]+' "$work/a.log" >"$work/b/.teamtype/config"
start b join
joiner=$last_pid
eventually b_has one || fail "the joiner did not receive the file"

# A restarted sharer keeps its history, so the joiner stays connected and gets new changes.
stop "$sharer"
start a share --no-join-code
sharer=$last_pid
sleep 2
echo two >"$work/a/f.txt"
eventually b_has two || fail "the joiner did not get a change after the sharer restarted"
kill -0 "$joiner" 2>/dev/null || fail "the joiner stopped after the sharer restarted with its history"

# A sharer that starts a new history: the joiner refuses to merge its own.
stop "$joiner"
stop "$sharer"
echo stale >"$work/b/f.txt"
start a share --init --no-join-code
sharer=$last_pid
sleep 2
echo three >"$work/a/f.txt"
start b join
joiner=$last_pid
eventually test ! -e "/proc/$joiner" || fail "the joiner with another history kept running"
grep -aq 'started a new history' "$work/b.log" || fail "the joiner did not say why it stopped"
[ "$(cat "$work/a/f.txt")" = three ] || fail "the joiner's stale file reached the sharer"
b_has stale || fail "the refusing joiner overwrote its own file"
start b join
eventually grep -aq 'Overwrite them?' "$work/b.log" || fail "joining again did not ask before overwriting"
(cd "$work/b" && echo y | exec "$TEAMTYPE_BINARY" join >>"$work/b.log" 2>&1) &
pids+=($!)
eventually b_has three || fail "joining again did not take the sharer's file"

exit "$((n_failures > 0))"
