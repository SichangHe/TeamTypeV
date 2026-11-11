#!/bin/sh
# Verifies the proof, then runs each negative control and checks it fails on the INTENDED obligation
# (file:line:col of the first error), not merely somewhere.
V=/hdd1/sichangheagent/vl_meeting_work/tools/verus-x86-linux/verus
cd "$(dirname "$0")" || exit 1
MEM=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
[ "$MEM" -ge 60 ] || { echo "need >=60 GiB MemAvailable, have $MEM"; exit 2; }
st=0
echo "== boundary.rs (expect: 0 errors)"
out=$(timeout 900 $V boundary.rs 2>&1)
echo "$out" | grep "verification results"
echo "$out" | grep -q " 0 errors" || st=1
# control : expected error position : what it checks
while read -r f pos why; do
  out=$(timeout 300 $V "negative/$f" 2>&1)
  res=$(echo "$out" | grep "verification results")
  if echo "$out" | grep -q -- "--> negative/$f:$pos" && echo "$res" | grep -q " 1 errors"; then
    echo "ok   $f fails at $pos ($why)"
  else
    echo "BAD  $f: expected exactly 1 error at $pos ($why); got: $res"
    echo "$out" | grep -A1 "^error" | head -4
    st=1
  fi
done <<'LIST'
n1_keep_old_deltas.rs 359:44 inv_buf preserved by dstep
n2_no_revive.rs 359:73 inv_m preserved by dstep
n3_no_disk_remove.rs 359:100 inv_disk preserved by dstep
n4_delete_keeps_cache.rs 118:39 rel_at preserved by cache_step
n5_bytes_keep_ownership.rs 359:44 inv_buf preserved by dstep
n6_no_final_write.rs 327:13 fin_get postcondition
LIST
exit $st
