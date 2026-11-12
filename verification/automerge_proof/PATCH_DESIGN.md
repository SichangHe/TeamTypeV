# Patch fidelity proof (`patch_fidelity.rs`)
(authored by agents unless marked 🧑)

Run: `verus patch_fidelity.rs`. Negative controls: `negative/patch_*.rs` (each must fail).

## Claim
For one received sync message and any file key `k`, starting from "cache/editor equals the doc before":
- `theorem_cache`: the `Document.files` cache after folding the patches equals the doc's value after the message (text, bytes, or absent). No `expect` in the fold panics (each `TextDelta::apply_to` is in bounds).
- `theorem_editor`: for a file open in an editor (the doc holds text `tb` before and the editor holds `tb`), the editor's text after applying the daemon's `file_deltas` equals the doc text after the message, or `""` if the file was deleted (the daemon re-creates it empty). Bytes are out of scope here.
- `example_conflict_switch`: the contract can be met by the case `replaced_text_objects_as_puts` exists for (visible object switched with only a `Conflict` patch). Both theorems apply to it, so the hypothesis is not vacuous.

## Model of TeamTypeV code (by reading, per key)
- `convert` = `replaced_text_objects_as_puts`. `before(k)` is `Text(w,_)` iff `k` is in `visible_text_objects()` (true under cache == doc).
- `step` = `PatchEffect::from_patch` plus the match in `receive_sync_message_log_patches`. PutMap(text), DeleteMap and an unsupported PutMap give FileRemoval. FileRemoval writes `""` if `text_obj` exists in the final doc and removes the entry otherwise. Bytes give FileBytes. Conflict gives NoEffect. Splice and DeleteSeq give a FileChange, which starts from `""` when the cache holds no string.
- `dstep` = daemon.rs `ReceiveSyncMessage`. FileRemoval runs `retain` (drop this file's deltas) and then pushes `delete(|content before|)`. FileChange pushes its delta.
- Edits use code-point indices. This is correct because automerge 0.10 without the `utf8-indexing`/`utf16-indexing` features uses `TextEncoding::UnicodeCodePoint` (`text_value.rs:12`; `cargo tree` shows only default features), and `apply_to` uses `chars()`.
- Projection to one key is by reading: each effect touches only its own path.

## Trusted Automerge patch contract (`am_contract`), from reading the vendored 0.10.0
- Order: all map-level patches come before all text-edit patches. Reason: `PatchLog::make_patches` stable-sorts events by object id (`patch_log.rs:442`). The `files` map is created in the initial doc, so it has a smaller id than any text object created later (Lamport counter). Exposed objects are flushed in id order as well (`ExposeQueue`).
- If the final value is text `(o,t)`, there are two cases:
  - Some "reset" patch for `k` exists: a PutMap of text, a DeleteMap, or a Conflict where the visible object changed. Then the edits for `k` turn `""` into `t`. New objects start empty, and exposed objects are emitted as a full splice at 0 (`flush_obj`).
  - No reset exists. Then the object is unchanged and the edits turn the old text into `t`.
  - In both cases, no bytes or unsupported put for `k` appears in the same message. This is stronger than the code needs. A probe test (bytes, then text, in one message) passed, but it was not kept.
- If the final value is bytes or absent, there are no edits for `k` (`get_path` drops events on objects that are not visible). The last non-Conflict map patch decides the value: PutBytes(b) gives the bytes, any other gives absent, and none means unchanged.
- Not proved: that Automerge's `make_patches` satisfies this contract. The 500-seed `fuzz_cache_stays_in_step_with_crdt` in document.rs is empirical evidence for it.

## Negative controls (each must fail)
- `patch_no_conflict_convert.rs`: without `replaced_text_objects_as_puts`, the conflict switch leaves the old text in place.
- `patch_removal_always_removes.rs`: FileRemoval that ignores the final doc drops files that were replaced by an empty peer file.
- `patch_editor_no_retain.rs`: the daemon without `retain`. Two removals then delete `|tb|` twice.
