#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Sichang He
#
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# Live trial of synchronized Git directories: a sharer with a Git repository and a joiner that
# starts empty. Checks that the joiner gets a working copy of the repository, that only the peer
# holding the version-control lock can commit, and that the lock passes on after its timeout.
# Needs `git` and a built `teamtype` (`cargo build -p teamtype`).
# Prints only failures; exit status 0 means every check passed.
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
TEAMTYPE_BINARY=${TEAMTYPE_BINARY:-$root/target/debug/teamtype}
export TEAMTYPE_VCS_LOCK_SECONDS=10
work=$(mktemp -d "${TMPDIR:-/tmp}/teamtype-git.XXXXXX")
pids=()
n_failures=0
cleanup() {
    kill "${pids[@]}" 2>/dev/null
    wait 2>/dev/null
    chmod -R u+w "$work" 2>/dev/null
    [ "$n_failures" -eq 0 ] && rm -rf "$work" || echo "kept $work" >&2
}
trap cleanup EXIT
fail() {
    echo "FAIL: $*" >&2
    n_failures=$((n_failures + 1))
}
# Poll until the command succeeds, for at most 60 s.
eventually() {
    for _ in $(seq 300); do
        "$@" && return 0
        sleep 0.2
    done
    return 1
}
in_dir() { (cd "$work/$1" && shift && "$@"); }
commit() { in_dir "$1" git -c user.name="$1" -c user.email="$1@x" commit -qam "$2" 2>/dev/null; }
head_is() { [ "$(in_dir "$1" git log -1 --format=%s 2>/dev/null)" = "$2" ]; }

mkdir -p "$work/a/.teamtype" "$work/b/.teamtype"
in_dir a git init -q
echo one >"$work/a/f.txt"
in_dir a git add f.txt
commit a init
(cd "$work/a" && exec "$TEAMTYPE_BINARY" share --no-join-code --show-secret-address \
    >"$work/a.log" 2>&1) &
pids+=($!)
eventually grep -aq 'peer=' "$work/a.log" || {
    fail "sharing daemon printed no secret address"
    exit 1
}
grep -aoE 'peer=[^ ]+' "$work/a.log" >"$work/b/.teamtype/config"
start_joiner() {
    (cd "$work/b" && exec "$TEAMTYPE_BINARY" join </dev/null >>"$work/b.log" 2>&1) &
    joiner_pid=$!
    pids+=($joiner_pid)
}
start_joiner

eventually head_is b init || fail "the joiner did not receive the repository"
eventually test -z "$(in_dir b git status --porcelain)" || fail "the joiner's working tree is not clean"

echo two >>"$work/b/f.txt"
commit b from-b || fail "the joiner could not commit while nobody held the lock"
eventually head_is a from-b || fail "the joiner's commit did not reach the sharer"
eventually grep -aq 'read-only' "$work/a.log" || fail "the sharer was not told about the lock"
echo three >>"$work/a/f.txt"
commit a from-a-early && fail "the sharer committed while the joiner held the lock"
head_is b from-b || fail "a refused commit changed the joiner's repository"

# A restarted lock holder still holds the lock.
kill "$joiner_pid" && wait "$joiner_pid" 2>/dev/null
start_joiner
sleep 3
echo four >>"$work/b/f.txt"
commit b from-b-again || fail "the lock holder could not commit after restarting"
eventually head_is a from-b-again || fail "the restarted holder's commit did not reach the sharer"

eventually grep -aq 'writable again' "$work/a.log" || fail "the lock did not time out"
echo five >>"$work/a/f.txt"
commit a from-a || fail "the sharer could not commit after the lock timed out"
eventually head_is b from-a || fail "the sharer's commit did not reach the joiner"
in_dir b git fsck --no-dangling >/dev/null 2>&1 || fail "the joiner's repository is corrupt"

exit "$((n_failures > 0))"
