#!/usr/bin/env bash
# Runs the correspondence check, then every proof listed in verus_targets.txt.
# usage: run_all.sh [repo-dir]    (repo-dir should be current main)
set -euo pipefail
cd -- "$(dirname -- "$0")"
REPO=${1:-/ssd1/sichangheagent/teamtype--teamtype}
V=${VERUS:-/hdd1/sichangheagent/vl_meeting_work/tools/verus-x86-linux/verus}
python3 -I corr.py check --repo "$REPO"
[ "${SKIP_VERUS:-0}" = 1 ] && exit 0
avail=$(awk '/MemAvailable:/ {print $2}' /proc/meminfo)
[ "$avail" -ge 62914560 ] || { echo "need >=60 GiB MemAvailable"; exit 2; }
fail=0
while read -r f extra; do
  case "$f" in ''|\#*) continue;; esac
  echo "== verus $f $extra"
  out=$(cd "$(dirname "$f")" && timeout 1800 "$V" $extra "$(basename "$f")" 2>&1) || true
  echo "$out" | grep 'verification results' || { echo "$out" | tail -5; }
  echo "$out" | grep -q 'verification results:: [0-9]* verified, 0 errors' || { echo "FAIL $f"; fail=1; }
done < verus_targets.txt
# trusted Ropey model tested against real Ropey with the repo's feature set
grep -q '^ropey = { version = "1", default-features = false }' "$REPO/crates/teamtype/Cargo.toml" \
  || { echo "FAIL crates/teamtype/Cargo.toml ropey features changed; update positions/ropey_axioms"; fail=1; }
echo "== ropey axioms test"
(cd ../positions/ropey_axioms && CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-/tmp/ropey_axioms_target} cargo run -q --release) 2>&1 | tail -3 | grep -q "200 random" || { echo "FAIL ropey axioms"; fail=1; }
# extra check scripts (e.g. negative controls); each must exit 0
while read -r s; do
  case "$s" in ''|\#*) continue;; esac
  echo "== $s"; sh "$s" || { echo "FAIL $s"; fail=1; }
done < extra_checks.txt
exit $fail
