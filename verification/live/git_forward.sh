#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Sichang He
# SPDX-License-Identifier: AGPL-3.0-or-later
# Real daemons: Git runs on the sharer, with no .git at either joiner.
# Needs a built teamtypev and Git. Prints only failures.
set -eu
root=$(cd "$(dirname "$0")/../.." && pwd)
export TEAMTYPEV_BINARY=${TEAMTYPEV_BINARY:-$root/target/debug/teamtypev}
work=$(mktemp -d "${TMPDIR:-/tmp}/teamtypev-git-forward.XXXXXX")
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
        sleep 0.2
    done
    return 1
}
in_dir() { local dir=$1; shift; (cd "$work/$dir" && "$@"); }
remote() { local dir=$1; shift; in_dir "$dir" "$TEAMTYPEV_BINARY" git "$@" </dev/null; }
start() {
    local dir=$1; shift
    (umask 000; cd "$work/$dir" && exec env GIT_DIR="$work/nonexistent" GIT_WORK_TREE="$work/nonexistent" "$TEAMTYPEV_BINARY" "$@" </dev/null >>"$work/$dir.log" 2>&1) &
    last_pid=$!
    pids+=("$last_pid")
}
has_text() { [ "$(cat "$work/$1/f.txt" 2>/dev/null)" = "$2" ]; }
mkdir -p "$work/a/.teamtypev" "$work/b/.teamtypev" "$work/c/.teamtypev"
in_dir a git init -q -b master
in_dir a git config user.name Sharer
in_dir a git config user.email sharer@example.test
printf 'one\n' >"$work/a/f.txt"
mkdir "$work/a/sub"
printf 'nested\n' >"$work/a/sub/n.txt"
in_dir a git add .
in_dir a git commit -qm initial
in_dir a git branch original
printf '#!/bin/sh\n# Installed by teamtypev\nexit 1\n' >"$work/a/.git/hooks/reference-transaction"
chmod +x "$work/a/.git/hooks/reference-transaction"
start a share --no-join-code --show-secret-address
sharer=$last_pid
eventually grep -aq 'peer=' "$work/a.log" || fail 'sharer printed no address'
for peer in b c; do
    grep -aoE 'peer=[^ ]+' "$work/a.log" >"$work/$peer/.teamtypev/config"
    start "$peer" join
    eventually has_text "$peer" one || fail "$peer did not receive initial files"
    [ ! -e "$work/$peer/.git" ] || fail "$peer received .git"
done
[ "$(stat -c %a "$work/a/.teamtypev/git.sock")" = 600 ] || fail 'socket permissions are not private'
[ "$(remote b rev-parse --show-toplevel)" = "$work/a" ] || fail 'inherited Git environment changed repository'
[ ! -e "$work/a/.git/hooks/reference-transaction" ] || fail 'legacy hook remains'
remote b status --porcelain >"$work/remote"
in_dir a git --no-pager -c color.ui=false status --porcelain >"$work/local"
cmp "$work/local" "$work/remote" || fail 'status differs'
printf 'two\n' >"$work/b/f.txt"
remote b diff >"$work/remote"
in_dir a git --no-pager -c color.ui=false diff >"$work/local"
cmp "$work/local" "$work/remote" || fail 'diff differs'
remote b add f.txt
remote b commit -qm forwarded
[ "$(in_dir a git show HEAD:f.txt)" = two ] || fail 'commit lacks edit'
[ "$(remote b log -1 --format=%s)" = forwarded ] || fail 'log lacks commit'
for n in $(seq 10); do
    printf 'immediate-%s\n' "$n" >"$work/b/f.txt"
    remote b commit -qam "barrier-$n"
    [ "$(in_dir a git show HEAD:f.txt)" = "immediate-$n" ] || fail "commit barrier lost edit $n"
done
remote b checkout -q original
has_text b one || fail 'checkout returned before files changed on first joiner'
for _ in $(seq 10); do
    remote b checkout -q master
    has_text b immediate-10 || fail 'checkout to master returned before files changed'
    remote b checkout -q original
    has_text b one || fail 'checkout to original returned before files changed'
done
eventually has_text c one || fail 'checkout did not change second joiner'
[ "$(in_dir b/sub "$TEAMTYPEV_BINARY" git ls-files)" = n.txt ] || fail 'relative working directory lost'
[ "$(in_dir b/sub ../.teamtypev/bin/git ls-files)" = n.txt ] || fail 'installed wrapper failed'
printf 'stdin bytes\000\377' >"$work/input"
in_dir b "$TEAMTYPEV_BINARY" git hash-object --stdin <"$work/input" >"$work/remote"
in_dir a git hash-object --stdin <"$work/input" >"$work/local"
cmp "$work/local" "$work/remote" || fail 'stdin differs'
set +e
remote b rev-parse --verify refs/heads/absent >"$work/remote" 2>"$work/remote.err"
remote_status=$?
in_dir a git --no-pager -c color.ui=false rev-parse --verify refs/heads/absent >"$work/local" 2>"$work/local.err"
local_status=$?
set -e
[ "$remote_status" = "$local_status" ] || fail 'exit status differs'
cmp "$work/local" "$work/remote" || fail 'failure stdout differs'
cmp "$work/local.err" "$work/remote.err" || fail 'failure stderr differs'
dd if=/dev/zero of="$work/input" bs=1048576 count=4 status=none
blob=$(in_dir a git hash-object -w --stdin <"$work/input")
remote b cat-file blob "$blob" >"$work/remote"
cmp "$work/input" "$work/remote" || fail 'large binary output differs'
remote b cat-file blob "$blob" | python3 -c 'import sys,time; time.sleep(3); data=sys.stdin.buffer.read(); assert data == bytes(4*1048576)' || fail 'slow consumer lost buffered output'
printf '%s\n' "$blob" | in_dir b "$TEAMTYPEV_BINARY" git cat-file '--batch-check=%(objectname)' >"$work/batch"
[ "$(cat "$work/batch")" = "$blob" ] || fail 'formatted batch stdin was lost'
set +e
remote b -h >"$work/help" 2>&1
help_status=$?
in_dir a git -h >"$work/local-help" 2>&1
local_help_status=$?
set -e
[ "$help_status" = "$local_help_status" ] || fail 'git -h exit differs'
cmp "$work/help" "$work/local-help" || fail 'git -h output differs'
printf '#!/bin/sh\n# Installed by teamtypev\nexit 1\n' >"$work/a/.git/hooks/reference-transaction"
chmod +x "$work/a/.git/hooks/reference-transaction"
remote b status >/dev/null
[ ! -e "$work/a/.git/hooks/reference-transaction" ] || fail 'hook created after startup remains'
in_dir a git config alias.serial '!printf start >> .teamtypev/order; sleep 1; printf end >> .teamtypev/order'
remote b serial &
first=$!
remote c serial &
second=$!
wait "$first" || fail 'first concurrent command failed'
wait "$second" || fail 'second concurrent command failed'
[ "$(cat "$work/a/.teamtypev/order")" = startendstartend ] || fail 'forwarded Git commands overlapped'
for option in '-C/' '-cfoo=bar' '--git-dir=/' '--work-tree=/' '--exec-path=/' '--namespace=x' '--config-env=x=y' '--super-prefix=x'; do
    set +e
    remote b "$option" status >"$work/rejected" 2>&1
    rejected_status=$?
    set -e
    [ "$rejected_status" = 129 ] || fail "global option $option returned $rejected_status"
    grep -q 'not allowed' "$work/rejected" || fail "no diagnostic for $option"
done
mkdir "$work/b/empty"
if in_dir b/empty "$TEAMTYPEV_BINARY" git status >"$work/empty.err" 2>&1; then fail 'empty directory unexpectedly exists on sharer'; fi
grep -q 'empty directories are not synchronized' "$work/empty.err" || fail 'unclear empty-directory diagnostic'
mkfifo "$work/pipe"
exec 9<>"$work/pipe"
in_dir a git config alias.signal '!kill -TERM $PPID; sleep 1'
set +e
remote b signal >"$work/signal.out" 2>&1
signal_status=$?
set -e
[ "$signal_status" = 143 ] || fail "signal exit status was $signal_status"
in_dir a git config alias.prompts '!test "$GIT_ASKPASS" = false && test "$SSH_ASKPASS" = false && test "$GIT_SSH_COMMAND" = "ssh -o BatchMode=yes"'
remote b prompts || fail 'prompt suppression environment is missing'
in_dir a git config alias.hang '!trap "sleep 1; rm -f .git/index.lock; exit 0" TERM INT; touch .git/index.lock; echo $$ > .teamtypev/hang.pid; sleep 180 & wait'
(cd "$work/b" && exec "$TEAMTYPEV_BINARY" git hang </dev/null >"$work/hang.out" 2>&1) &
cancel_pid=$!
pids+=("$cancel_pid")
eventually test -s "$work/a/.teamtypev/hang.pid" || fail 'hung command did not start'
kill "$cancel_pid"
wait "$cancel_pid" 2>/dev/null || true
eventually test ! -e "$work/a/.git/index.lock" || fail 'cancel skipped graceful cleanup'
timeout 5s bash -c 'cd "$1" && "$2" git status </dev/null' _ "$work/b" "$TEAMTYPEV_BINARY" >"$work/after-cancel" || fail 'cancelled command blocked queue'
in_dir a git config alias.background '!sleep 180 &'
timeout 5s bash -c 'cd "$1" && "$2" git background </dev/null' _ "$work/b" "$TEAMTYPEV_BINARY" || fail 'inherited pipes blocked completion'
in_dir a git config alias.long '!sleep 121'
timeout 140s bash -c 'cd "$1" && "$2" git long </dev/null' _ "$work/b" "$TEAMTYPEV_BINARY" >"$work/long.out" 2>&1 || fail 'long command was cancelled'
printf -v log_format '%65536s' ''
set +e
(set -o pipefail; remote b log --all --format="format:$log_format%H" | head -n 1 >/dev/null) 2>"$work/broken.err"
pipe_status=$?
(set -o pipefail; in_dir a git log --all --format="format:$log_format%H" | head -n 1 >/dev/null) 2>"$work/local-broken.err"
local_pipe_status=$?
set -e
[ "$pipe_status" = "$local_pipe_status" ] || fail "broken pipe exit status was $pipe_status, expected $local_pipe_status"
[ ! -s "$work/broken.err" ] || fail 'broken pipe printed an error'
git -C "$work" init -q
mv "$work/a/.git" "$work/a/.teamtypev/repo"
if remote b status >"$work/parent.out" 2>&1; then fail 'discovered parent repository'; fi
grep -q 'own Git repository' "$work/parent.out" || fail 'missing repository boundary diagnostic'
mv "$work/a/.teamtypev/repo" "$work/a/.git"
(cd "$work/b" && exec "$TEAMTYPEV_BINARY" git cat-file blob "$blob" </dev/null >&9 2>"$work/stalled.err") &
stalled_pid=$!
pids+=("$stalled_pid")
sleep 1
printf 'sync while stalled\n' >"$work/c/f.txt"
eventually has_text b 'sync while stalled' || fail 'stalled output blocked document sync'
kill "$stalled_pid" 2>/dev/null || true
wait "$stalled_pid" 2>/dev/null || true
exec 9>&-
if remote b commit --allow-empty >"$work/editor.out" 2>&1; then fail 'interactive editor unexpectedly succeeded'; fi
grep -q 'editor' "$work/editor.out" || fail 'missing editor diagnostic'
kill "$sharer"
wait "$sharer" 2>/dev/null || true
if timeout 15s bash -c 'cd "$1" && "$2" git status </dev/null' _ "$work/b" "$TEAMTYPEV_BINARY" >"$work/offline" 2>&1; then
    fail 'offline command succeeded'
fi
grep -Eq 'offline|lost|did not answer' "$work/offline" || fail 'offline command lacked a diagnostic'
for peer in b c; do [ ! -e "$work/$peer/.git" ] || fail "$peer acquired .git"; done
success=yes
