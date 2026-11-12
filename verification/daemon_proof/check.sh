#!/bin/sh
# Verifies the proof and runs the negative controls (each must report errors).
V=${VERUS:-verus}
cd "$(dirname "$0")" || exit 1
avail=$(awk '/MemAvailable/ {print int($2/1048576)}' /proc/meminfo)
[ "$avail" -ge 60 ] || { echo "need >=60 GiB MemAvailable, have $avail"; exit 1; }
for f in daemon_proof.rs disk_proof.rs disk_full.rs panic_proof.rs tp1_id.rs; do echo "== $f (expect: 0 errors)"; timeout 900 $V $f 2>&1 | grep "verification results"; done
for f in negative/*.rs; do
  echo "== $f (expect: errors)"
  timeout 300 $V "$f" 2>&1 | grep "verification results"
done
echo "== diff_proof.rs (expect: 4 verified, 0 errors; imports tp1_id.rs, --verify-root verifies only this file)"
timeout 600 $V diff_proof.rs --verify-root 2>&1 | grep "verification results"
echo "== panic_wired.rs (expect: 76 verified, 0 errors; negative/wired_editor_edit_unchecked.rs must error)"
timeout 900 $V panic_wired.rs 2>&1 | grep "verification results"
