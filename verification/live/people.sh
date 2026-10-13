#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Sichang He
#
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# Live trial: `N_PEOPLE` (default 4, at least 3) `teamtype` daemon processes, one headless Neovim
# with the real plugin per daemon. Everyone types into one file at once; agent command line edits
# follow; then a joiner and the sharer each drop out and return while the others keep typing.
# Needs `nvim`, `python3`, and a built `teamtype` (`cargo build -p teamtype`); `N_ROUNDS` sets
# the lines each person types per phase.
# Prints only failures; exit status 0 means every check passed.
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
export TEAMTYPE_BINARY=${TEAMTYPE_BINARY:-$root/target/debug/teamtype}
n_rounds=${N_ROUNDS:-20}
all_people=(a b c d e f g h)
people=("${all_people[@]:0:${N_PEOPLE:-4}}")
sharer=a
joiner=${people[-1]}
work=$(mktemp -d "${TMPDIR:-/tmp}/teamtype-live.XXXXXX")
declare -A daemon_pid nvim_pid
n_failures=0
cleanup() {
    kill "${daemon_pid[@]}" "${nvim_pid[@]}" 2>/dev/null
    wait 2>/dev/null
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
start_daemon() {
    local command=(join)
    [ "$1" = "$sharer" ] && command=(share --no-join-code --show-secret-address)
    (cd "$work/$1" && exec "$TEAMTYPE_BINARY" "${command[@]}" >>"$work/$1.log" 2>&1) &
    daemon_pid[$1]=$!
}
start_nvim() {
    (cd "$work/$1" && exec nvim --headless --clean -n --listen "$work/$1.nvim" \
        --cmd "set runtimepath^=$root/nvim-plugin" shared.txt >>"$work/$1.nvim.log" 2>&1) &
    nvim_pid[$1]=$!
    eventually test -S "$work/$1.nvim" || fail "Neovim $1 did not start"
}
# The editor leaves first so that its daemon writes the file to disk.
drop() {
    kill "${nvim_pid[$1]}" && wait "${nvim_pid[$1]}"
    kill "${daemon_pid[$1]}" && wait "${daemon_pid[$1]}"
    rm -f "$work/$1.nvim"
}
rejoin() {
    start_daemon "$1"
    eventually test -S "$work/$1/.teamtype/socket" || fail "daemon $1 did not come back"
    start_nvim "$1"
}
nvim_expr() {
    nvim --server "$work/$1.nvim" --remote-expr "$2"
}
buffer() {
    nvim_expr "$1" 'join(getline(1, "$"), "\n")'
}
# Start typing `n_rounds` lines `PREFIX-ROUND` in one person's Neovim; `typists` collects the jobs.
typists=()
type_lines() {
    (for round in $(seq "$n_rounds"); do
        nvim_expr "$1" "nvim_buf_set_lines(0, 1, 1, 0, ['$2-$round'])" >/dev/null
    done) &
    typists+=($!)
}
finish_typing() {
    wait "${typists[@]}"
    typists=()
}
# Every Neovim buffer is identical and holds exactly COUNT lines matching PATTERN.
buffers_agree_with() {
    local text person
    text=$(buffer "$sharer")
    [ "$(grep -c "$1" <<<"$text")" -eq "$2" ] || return 1
    for person in "${people[@]:1}"; do
        [ "$text" = "$(buffer "$person")" ] || return 1
    done
}
files_agree() {
    local person
    grep -q "$2" "$work/$sharer/$1" 2>/dev/null || return 1
    for person in "${people[@]:1}"; do
        cmp -s "$work/$sharer/$1" "$work/$person/$1" || return 1
    done
}
agent_edit() {
    "$TEAMTYPE_BINARY" agent-edit --directory "$work/$1" --file "$2" \
        --expected "$3" --replacement "$4" 2>>"$work/agent.log"
}
dump_buffers() {
    local person
    for person in "${people[@]}"; do buffer "$person" >"$work/$person.buffer"; done
    wc -l "$work"/?.buffer >&2
}

for person in "${people[@]}"; do mkdir -p "$work/$person/.teamtype"; done
echo seed >"$work/$sharer/shared.txt"
printf 'v1\n' >"$work/$sharer/agent.txt"
start_daemon "$sharer"
eventually grep -q 'peer=' "$work/$sharer.log" || {
    fail "sharing daemon printed no secret address"
    exit 1
}
for person in "${people[@]:1}"; do
    grep -oE 'peer=[^ ]+' "$work/$sharer.log" >"$work/$person/.teamtype/config"
    start_daemon "$person"
done
eventually files_agree shared.txt seed || {
    fail "joining daemons did not receive the shared file"
    tail -n 20 "$work"/?.log >&2
    exit 1
}

for person in "${people[@]}"; do start_nvim "$person"; done
sleep 2
for person in "${people[@]}"; do type_lines "$person" "$person"; done
finish_typing
n_lines=$((${#people[@]} * n_rounds))
eventually buffers_agree_with '^[a-h]-[0-9]*$' "$n_lines" || {
    fail "Neovim buffers did not converge on all $n_lines typed lines"
    dump_buffers
}

# Agent edits to a file no editor has open, from a joiner and from the sharer, reach everyone;
# a stale snapshot changes nothing.
agent_edit b agent.txt $'v1\n' $'v2\n' || fail "agent edit in a joining directory was rejected"
eventually files_agree agent.txt v2 || fail "agent edit from a joiner did not reach the others"
agent_edit "$sharer" agent.txt $'v2\n' $'v3\n' || fail "agent edit in the sharing directory was rejected"
eventually files_agree agent.txt v3 || fail "agent edit from the sharer did not reach the others"
agent_edit c agent.txt $'v1\n' $'lost\n' && fail "agent edit with a stale snapshot was accepted"
agent_edit c missing.txt old new && fail "agent edit to a missing file was accepted"
[ -e "$work/c/missing.txt" ] && fail "agent edit created a missing file"
sleep 1
files_agree agent.txt v3 || fail "stale agent edit changed the file"

# Agent edits to the file every Neovim has open, while the sharer's Neovim keeps typing.
# The agent rereads and retries when the file changed under it, as a real agent would.
agent_append() {
    snapshot=$(buffer c)$'\n'
    agent_edit c shared.txt "$snapshot" "${snapshot}agent-line"$'\n'
}
type_lines "$sharer" late
eventually agent_append || fail "agent edit to an editor-open file was rejected"
finish_typing
eventually buffers_agree_with '^agent-line$' 1 || fail "agent edit did not reach every Neovim buffer"
buffers_agree_with '^late-[0-9]*$' "$n_rounds" || fail "agent edit lost lines typed at the same time"
agent_edit b shared.txt "$snapshot" "gone" && fail "stale agent edit to an editor-open file was accepted"
sleep 1
buffers_agree_with '^agent-line$' 1 || fail "stale agent edit changed the editor-open file"
[ "$(grep -c 'file changed since the supplied snapshot' "$work/agent.log")" -ge 2 ] ||
    fail "stale agent edits were not rejected for being stale"

# One person drops out mid-edit and returns: first a joiner, then the sharer, through whom the
# others reach each other. The rest type before, during, and after the absence.
for dropped in "$joiner" "$sharer"; do
    for person in "${people[@]}"; do
        [ "$person" = "$dropped" ] || type_lines "$person" "while-$dropped-away-$person"
    done
    sleep 0.3
    drop "$dropped"
    finish_typing
    rejoin "$dropped"
    type_lines "$dropped" "$dropped-back"
    finish_typing
    n_lines=$(((${#people[@]} - 1) * n_rounds))
    eventually buffers_agree_with "^while-$dropped-away-[a-h]-[0-9]*\$" "$n_lines" || {
        fail "lines typed while $dropped was away did not reach everyone"
        dump_buffers
    }
    eventually buffers_agree_with "^$dropped-back-[0-9]*\$" "$n_rounds" ||
        fail "lines typed by $dropped after returning did not reach everyone"
done

# An editor that vanishes with requests still queued must not take its daemon down.
python3 - "$work/c" <<'PYTHON'
import json, socket, sys
directory = sys.argv[1]
uri = f"file://{directory}/shared.txt"
requests = [{"jsonrpc": "2.0", "id": 1, "method": "open", "params": {"uri": uri, "content": ""}}]
requests += [
    {"jsonrpc": "2.0", "id": i, "method": "cursor", "params": {"uri": uri, "ranges": []}}
    for i in range(2, 200)
]
client = socket.socket(socket.AF_UNIX)
client.connect(f"{directory}/.teamtype/socket")
client.sendall("".join(json.dumps(request) + "\n" for request in requests).encode())
client.close()
PYTHON
nvim_expr "$sharer" "nvim_buf_set_lines(0, 1, 1, 0, ['after-vanish'])" >/dev/null
eventually buffers_agree_with '^after-vanish$' 1 || fail "editing stopped after an editor vanished"
for person in "${people[@]}"; do
    kill -0 "${daemon_pid[$person]}" 2>/dev/null || fail "daemon $person died"
done

exit "$((n_failures > 0))"
