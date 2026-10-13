#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Sichang He
#
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# Live trial: three `teamtype` daemon processes, one headless Neovim with the real plugin per
# daemon, all typing into one file at once, then agent command line edits.
# Needs `nvim`, `python3`, and a built `teamtype` (`cargo build -p teamtype`); set `N_ROUNDS` to type more.
# Prints only failures; exit status 0 means every check passed.
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
export TEAMTYPE_BINARY=${TEAMTYPE_BINARY:-$root/target/debug/teamtype}
n_rounds=${N_ROUNDS:-20}
people=(a b c)
work=$(mktemp -d "${TMPDIR:-/tmp}/teamtype-live.XXXXXX")
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
# Poll until the command succeeds, for at most 30 s.
eventually() {
    for _ in $(seq 150); do
        "$@" && return 0
        sleep 0.2
    done
    return 1
}
daemon() {
    (cd "$work/$1" && exec "$TEAMTYPE_BINARY" "${@:2}" >"$work/$1.log" 2>&1) &
    pids+=($!)
}
nvim_expr() {
    nvim --server "$work/$1.nvim" --remote-expr "$2"
}
buffer() {
    nvim_expr "$1" 'join(getline(1, "$"), "\n")'
}
buffers_agree_with() {
    local want=$1 text_a
    text_a=$(buffer a)
    [ "$(grep -c "$want" <<<"$text_a")" -eq "$2" ] &&
        [ "$text_a" = "$(buffer b)" ] && [ "$text_a" = "$(buffer c)" ]
}
files_agree() {
    grep -q "$2" "$work/a/$1" 2>/dev/null &&
        cmp -s "$work/a/$1" "$work/b/$1" && cmp -s "$work/a/$1" "$work/c/$1"
}
agent_edit() {
    "$TEAMTYPE_BINARY" agent-edit --directory "$work/$1" --file "$2" \
        --expected "$3" --replacement "$4" 2>>"$work/agent.log"
}

for person in "${people[@]}"; do mkdir -p "$work/$person/.teamtype"; done
echo seed >"$work/a/shared.txt"
printf 'v1\n' >"$work/a/agent.txt"
daemon a share --no-join-code --show-secret-address
eventually grep -q 'peer=' "$work/a.log" || {
    fail "sharing daemon printed no secret address"
    exit 1
}
grep -oE 'peer=[^ ]+' "$work/a.log" | tee "$work/b/.teamtype/config" >"$work/c/.teamtype/config"
daemon b join
daemon c join
eventually files_agree shared.txt seed || {
    fail "joining daemons did not receive the shared file"
    tail -n 20 "$work"/?.log >&2
    exit 1
}

for person in "${people[@]}"; do
    (cd "$work/$person" && exec nvim --headless --clean -n --listen "$work/$person.nvim" \
        --cmd "set runtimepath^=$root/nvim-plugin" shared.txt >"$work/$person.nvim.log" 2>&1) &
    pids+=($!)
done
for person in "${people[@]}"; do
    eventually test -S "$work/$person.nvim" || fail "Neovim $person did not start"
done
sleep 2
typists=()
for person in "${people[@]}"; do
    (for round in $(seq "$n_rounds"); do
        nvim_expr "$person" "nvim_buf_set_lines(0, 1, 1, 0, ['$person-$round'])" >/dev/null
    done) &
    typists+=($!)
done
wait "${typists[@]}"
eventually buffers_agree_with '^[abc]-[0-9]*$' $((3 * n_rounds)) || {
    fail "Neovim buffers did not converge on all $((3 * n_rounds)) typed lines"
    for person in "${people[@]}"; do buffer "$person" >"$work/$person.buffer"; done
    wc -l "$work"/?.buffer >&2
}

# Agent edits to a file no editor has open, from a joiner and from the sharer, reach everyone;
# a stale snapshot changes nothing.
agent_edit b agent.txt $'v1\n' $'v2\n' || fail "agent edit in a joining directory was rejected"
eventually files_agree agent.txt v2 || fail "agent edit from b did not reach a and c"
agent_edit a agent.txt $'v2\n' $'v3\n' || fail "agent edit in the sharing directory was rejected"
eventually files_agree agent.txt v3 || fail "agent edit from a did not reach b and c"
agent_edit c agent.txt $'v1\n' $'lost\n' && fail "agent edit with a stale snapshot was accepted"
agent_edit c missing.txt old new && fail "agent edit to a missing file was accepted"
[ -e "$work/c/missing.txt" ] && fail "agent edit created a missing file"
sleep 1
files_agree agent.txt v3 || fail "stale agent edit changed the file"

# Agent edits to the file all three Neovims have open, while Neovim a keeps typing.
# The agent rereads and retries when the file changed under it, as a real agent would.
agent_append() {
    snapshot=$(buffer c)$'\n'
    agent_edit c shared.txt "$snapshot" "${snapshot}agent-line"$'\n'
}
(for round in $(seq "$n_rounds"); do
    nvim_expr a "nvim_buf_set_lines(0, 1, 1, 0, ['late-$round'])" >/dev/null
done) &
typist=$!
eventually agent_append || fail "agent edit to an editor-open file was rejected"
wait "$typist"
eventually buffers_agree_with '^agent-line$' 1 || fail "agent edit did not reach every Neovim buffer"
buffers_agree_with '^late-[0-9]*$' "$n_rounds" || fail "agent edit lost lines typed at the same time"
agent_edit b shared.txt "$snapshot" "gone" && fail "stale agent edit to an editor-open file was accepted"
sleep 1
buffers_agree_with '^agent-line$' 1 || fail "stale agent edit changed the editor-open file"
[ "$(grep -c 'file changed since the supplied snapshot' "$work/agent.log")" -ge 2 ] ||
    fail "stale agent edits were not rejected for being stale"

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
nvim_expr a "nvim_buf_set_lines(0, 1, 1, 0, ['after-vanish'])" >/dev/null
eventually buffers_agree_with '^after-vanish$' 1 || fail "editing stopped after an editor vanished"
for index in 0 1 2; do
    kill -0 "${pids[$index]}" 2>/dev/null || fail "daemon ${people[$index]} died"
done

exit "$((n_failures > 0))"
