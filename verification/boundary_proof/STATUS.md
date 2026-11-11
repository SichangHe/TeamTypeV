# boundary_proof STATUS
(authored by agents unless marked 🧑)

Updated 2026-11-11 08:10 PST (third pass). Earlier pass timestamps in this file were wrong; real clock was ~08:00-08:05. Reran `./check.sh` this morning: all results below reproduced.

## State found
- night agent left boundary.rs, cache.rs, check.sh, negative/n1-n6; no STATUS.md or design doc
- no `admit`/`assume`/`external_body` in boundary.rs
- cache.rs is the earlier, smaller model (cache vs CRDT only); boundary.rs includes it (same defs plus daemon layer), so cache.rs is superseded

## Proved (boundary.rs, 23 verified, 0 errors)
Model: one `ReceiveSyncMessage` in daemon.rs (git not running, writes succeed) plus `Document::receive_sync_message_log_patches` in document.rs.
- `step_preserves` / `replay_preserves`: starting from cache == CRDT, applying the per-patch cache updates (PutText, PutBytes, Delete, Splice, DelSeq, Conflict) yields cache == final document `f`; no cache delta ever misfits (the Rust would panic)
- `receive_sync_message_correct`, for any patch sequence replaying `c0` to `f`:
  1. cache == `f`, except files an editor holds open that were deleted/replaced are revived as empty text
  2. every editor still owning a file: its buffer after the forwarded OT deltas == cache text (OT/CRDT boundary)
  3. after the final disk writes, disk == cache for every non-excluded file no editor owns
- deltas forwarded to editors always fit their buffers (`app_ok`)

## Assumptions (pre) and trusted base
- Automerge patch log semantics are ASSUMED: `step_view` is the specified replay of patches; Automerge convergence and patch-log correctness are unproved
- patches are already in the shape types.rs accepts (including the `replaced_text_objects_as_puts` rewrite); types.rs parsing is not modelled
- before the message: an editor owning a file holds exactly the daemon text; disk == cache for unowned non-excluded files. In-flight OT is the `concurrency/` proof's job; the invariant between messages is assumed, not proved here
- git-running mode, failed writes, multiple messages in sequence, async interleaving, editor-rejected changes: not modelled
- paths are abstract naturals; text is a sequence of ints (no UTF-8/UTF-16 offset conversion)
- Rust code is modelled by hand, not extracted; fidelity is by reading, not by tool

## Negative controls (each must fail; all fail with 15 verified, 1 error)
- n1 keeps old deltas on delete/replace
- n2 never revives the cache for an owned file
- n3 never removes the file from disk
- n4 Delete does not update the cache
- n5 PutBytes keeps editor ownership
- n6 skips the final write of pending files
Each removes one mechanism of the fix in 6146e00, so the theorem needs each.

## Bugs fixed
- 6146e00 "stop recreated files being deleted and concurrent-create conflicts corrupting the cache" (daemon.rs, document.rs, editor_connection.rs, test daemon_race_tests.rs). The proof's mechanisms (revival, delta reset on replace, cache set from final doc) mirror this fix. Found by the randomized race test, not by Verus
- no new bugs found this session

## Added in second pass (boundary.rs)
- message sequences, cache layer: `message_sequence`. For any `c` within `drift` of CRDT `v` (cache equals CRDT, or holds empty text where CRDT lacks the file: the editor-revived files) and any message replaying `v` to `f`, no delta misfits and the result is within `drift` of `f`. So the invariant is closed under consecutive messages. Uses `rel2`, `step_preserves2`, `replay_preserves2`
- git running: `git_running_correct`. write_file only records `deferred_writes` (daemon.rs `write_file`), so disk is untouched; every unowned (at start), non-excluded path the message did not touch (`done`) already has disk == cache. Touched paths are the deferred set (superset of what the non-git run writes)
- types.rs/UTF: the daemon core counts Unicode scalar values (`chars().count()` in document.rs, daemon.rs, ot.rs, types.rs), which is exactly the model's `Seq<int>` unit. UTF-16/editor-position conversion is in types.rs; not re-proved here, see ../positions
- negative controls n1-n6 are unchanged copies of the first-pass model and still fail as required; the new lemmas have no negative control of their own

## Review (fresh subagent, read-only; it read code and model but did not run Verus)
- verdict: non-vacuous (pre satisfiable, e.g. own0={} and disk0=c0; no contradictory requires; no admit/assume); no definite real bug
- fidelity: FileRemoval order/branches, revival, delta reset, PutBytes invalidation, fin_write dedup all match daemon.rs/document.rs
- noted weaknesses, not fixed
  - `replay_preserves` (document.rs) is not invoked by the daemon theorem, which just starts from cache == f; the chaining is sound by reading, not enforced
  - claim (2) says buf0 + forwarded deltas == cache text, a necessary condition for OT, not OT itself (ot_server transforms and in-flight ops are concurrency/'s)
  - check.sh greps only the results line, so a negative control failing from a syntax error would not be distinguished from the intended failure; not individually checked
  - `assert(... || true)` in step_preserves is a no-op
  - possible race outside the claim: `try_write_file` calls `file_created_or_changed`, which can `merge_disk_content`/`file_removed` and mutate the CRDT mid-loop when `disk_content` differs from disk (pending watcher event). The model's pre (disk == cache, disk_content ignored) rules this window out
  - unchecked assumption: editors never own excluded paths (pre); real Open path not checked
  - unmodelled: send_to_editor_client failure removes editor and releases files; panics on unsupported patch shapes (types.rs from_crdt_patches, borrowed-bytes PutMap)
  - Splice/DelSeq indices are char indices in the model; Automerge text units may differ

## Third pass
- chaining: `init_cache_justified` proves the document.rs per-patch cache update yields exactly `f`, which is what `init_d` assumed; `pipeline_correct` composes it with `receive_sync_message_correct`. The daemon theorem's start state is now derived, not assumed (given pre)
- check.sh now (a) refuses to run below 60 GiB MemAvailable, (b) requires each negative control to fail with exactly 1 error at the intended obligation (file:line:col), and exits nonzero otherwise. Verified: n1 and n5 break inv_buf, n2 inv_m, n3 inv_disk, n4 rel_at under cache_step, n6 the fin_get postcondition
- disk-content race (reviewer's top item): read daemon.rs. `try_write_file` calling `file_created_or_changed` -> `merge_disk_content` is deliberate three-way merge of outside edits ("Merges outside changes before writing shared text"); it mutates the CRDT through `update_text`/`set_file`/`remove_file`, which all update the `files` cache in the same call, so cache == CRDT is preserved, and the write loop re-reads `current_file_content` until stable. Not shown to be a bug. Empirical: the existing randomized race test (`daemon_race_tests.rs`, includes disk writes without watcher events, disk removes/creates, editor open/close) was run at 3000 seeds each for the 2-peer and 3-peer tests (default 60/40): all pass (207 s). So no reproducer, no code change, no commit this pass
- still unproved for that path: that the `disk_edits` delta from `merge_disk_content` mid-loop reaches editors in an order consistent with the already-queued `file_deltas` when an editor owns the file (the random test exercises it; the proof does not)

## Remains
- model `disk_content` and the merge feedback in the proof (not just test it); failed writes (logged, not retried)
- daemon-layer theorem from a drifted cache (cache layer already handles drift: `message_sequence`)
- compose between-message editor invariant with concurrency/ (needs shared refinement)
- types.rs patch classification and replaced_text_objects_as_puts assumed
- async interleaving, editor-rejected changes, editor-drop ownership release, multiple daemons
- editors never own excluded paths is assumed in pre; Open path not checked
