#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Sichang He
#
# SPDX-License-Identifier: AGPL-3.0-or-later
#
# Live trial: a real Emacs (docker image `silex/emacs:29`) on a joining daemon and a headless
# Neovim on the sharing daemon type into one file at once; both buffers must end up equal and
# hold every typed line; then Emacs must report its daemon being killed.
# Usage: emacs-plugin/test.sh [path/to/teamtype]
# Prints only failures; exit status 0 means every check passed.
set -u
here=$(cd "$(dirname "$0")" && pwd)
export TEAMTYPE_BINARY
TEAMTYPE_BINARY=$(realpath "${1:-$here/../target/debug/teamtype}")
n_rounds=${N_ROUNDS:-20}
work=$(mktemp -d "${TMPDIR:-/tmp}/teamtype-emacs.XXXXXX")
pids=()
cleanup() {
    status=$?
    kill "${pids[@]}" 2>/dev/null
    docker rm -f "teamtype-emacs-$$" >/dev/null 2>&1
    wait 2>/dev/null
    [ "$status" -eq 0 ] && rm -rf "$work" || echo "kept $work" >&2
}
trap cleanup EXIT
fail() {
    echo "FAIL: $*" >&2
    tail -n 15 "$work"/*.log >&2
    exit 1
}
# Poll until the command succeeds, for at most 60 s.
eventually() {
    for _ in $(seq 300); do
        "$@" && return 0
        sleep 0.2
    done
    return 1
}
nvim_expr() {
    nvim --server "$work/a.nvim" --remote-expr "$1"
}
buffers_agree() {
    [ "$(nvim_expr 'join(getline(1, "$"), "\n")')" = "$(cat "$work/emacs.buffer")" ]
}

mkdir -p "$work"/{a,b}/.teamtype
echo seed >"$work/a/file.txt"
(cd "$work/a" && exec "$TEAMTYPE_BINARY" share --no-join-code --show-secret-address >"$work/a.log" 2>&1) &
pids+=($!)
eventually grep -q 'peer=' "$work/a.log" || fail "sharing daemon printed no secret address"
grep -oE 'peer=[^ ]+' "$work/a.log" >"$work/b/.teamtype/config"
(cd "$work/b" && exec "$TEAMTYPE_BINARY" join >"$work/b.log" 2>&1) &
pids+=($!)
eventually grep -qs seed "$work/b/file.txt" || fail "joining daemon did not receive the file"
(cd "$work/a" && exec nvim --headless --clean -n --listen "$work/a.nvim" \
    --cmd "set runtimepath^=$here/../nvim-plugin" file.txt >"$work/nvim.log" 2>&1) &
pids+=($!)

cat >"$work/driver.el" <<'EOF'
(defun work-file (name) (concat (getenv "WORK") "/" name))
(defun wait-for (pred secs)
  (let ((end (+ (float-time) secs)))
    (while (and (< (float-time) end) (not (funcall pred)))
      (accept-process-output nil 0.1))
    (funcall pred)))
(defun n-typed-lines () (how-many "^[ae]-[0-9]+$" (point-min) (point-max)))
(find-file (work-file "b/file.txt"))
(unless (wait-for (lambda () (and teamtype--client (string-match-p "seed" (buffer-string)))) 20)
  (message "DRIVER: buffer is not tracked") (kill-emacs 2))
(write-region "" nil (work-file "ready"))
(wait-for (lambda () (file-exists-p (work-file "go"))) 60)
(let ((n-rounds (string-to-number (getenv "N_ROUNDS"))))
  (dotimes (round n-rounds)
    (goto-char (point-min))
    (forward-line 1)
    (insert (format "e-%d\n" round))
    (accept-process-output nil 0.05))
  (unless (wait-for (lambda () (= (n-typed-lines) (* 2 n-rounds))) 60)
    (message "DRIVER: %d of %d typed lines arrived" (n-typed-lines) (* 2 n-rounds))
    (kill-emacs 3)))
(write-region (buffer-string) nil (work-file "emacs.buffer"))
(unless (wait-for (lambda () buffer-read-only) 60)
  (message "DRIVER: the daemon's death did not make the buffer read-only") (kill-emacs 4))
(kill-emacs 0)
EOF
# Emacs runs as the invoking user; the work directory keeps its path because the daemon
# rejects files outside its shared directory.
docker run --rm --name "teamtype-emacs-$$" --user "$(id -u):$(id -g)" -e HOME=/tmp \
    -e WORK="$work" -e N_ROUNDS="$n_rounds" -v "$TEAMTYPE_BINARY:/usr/local/bin/teamtype:ro" \
    -v "$work:$work" -v "$here:/plugin:ro" silex/emacs:29 \
    emacs --batch -L /plugin -l teamtype -l "$work/driver.el" >"$work/emacs.log" 2>&1 &
emacs_pid=$!

eventually test -e "$work/ready" || fail "Emacs did not open the shared file"
touch "$work/go"
for round in $(seq "$n_rounds"); do
    nvim_expr "nvim_buf_set_lines(0, 1, 1, 0, ['a-$round'])" >/dev/null
done
eventually test -e "$work/emacs.buffer" || fail "Emacs did not receive every typed line"
eventually buffers_agree || fail "Emacs and Neovim buffers differ"
# Emacs must notice its daemon dying under it and refuse further edits.
kill -9 "${pids[1]}"
wait "$emacs_pid" || fail "Emacs did not react to its daemon's death"
grep -q 'Connection to Teamtype daemon .* lost' "$work/emacs.log" || fail "Emacs did not report the lost daemon"
[ "$(grep -c '^[ae]-[0-9]*$' "$work/emacs.buffer")" -eq $((2 * n_rounds)) ] ||
    fail "typed lines are missing"
