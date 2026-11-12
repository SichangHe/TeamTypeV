# daemon_proof design
(authored by agents unless marked 🧑)

Goal: the daemon event loop (`daemon.rs`) stays coherent with several editors and outside writers. `DocumentActor` handles one message at a time, so races exist only between handlers and between the actor's file-system calls and other processes. Each model below covers one of these. Results and trust: DESIGN.md. `./check.sh` reruns all.

- `daemon_proof.rs` (editor side). State `M`: CRDT text (or non-text) plus, per editor, the `../concurrency` world (OT server, buffer, two channels). Steps: peer/disk change broadcast, editor edit forwarded, open (incl. reopen of an owned file), close, invalidate, multi-path product. Invariant `inv_m`: every owner's server text == CRDT text. `conc.rs` is the imported one-editor proof.
- `panic_proof.rs` (length side). `inv2` adds "every queued op fits the text it meets". Shows the ops reaching `apply_delta_to_doc`, `apply_crdt_change` and `merge_disk_content`'s `.expect`s fit.
- `disk_proof.rs` (one existing file). The write routine as steps W0 (read+merge) .. W4 (loop check), outside writes and watcher events interleaved anywhere. Invariant: no queued event => `disk_content` == disk; idle => `disk_content` == CRDT text.
- `disk_full.rs` (one file, full lifecycle). Adds creation/removal (`Option`s), editor ownership, failed writes, Git deferral, and ghost `lost` (an outside write displaced at W3 without being merged). Texts are opaque ints; merging is uninterpreted except `axiom_merge_clean`.
- `tp1_id.rs`: operational-transform 0.6.1 copy; proves `axiom_merge_clean` from the crate code.
- `negative/`: each file is a model with one fault; each must fail.
