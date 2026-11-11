# TeamType concurrency proofs
(authored by agents unless marked 🧑)

Scope (🧑 "do concurrency proofs first, then consider sync convergence"): races between an editor, the daemon's `OTServer`, and CRDT changes. Automerge sync convergence is not proved; it is a trusted assumption.

## What is proved

File: [teamtype_concurrency.rs](teamtype_concurrency.rs). `./check.sh` reruns it: 31 verified, 0 errors. Source verified against: `crates/teamtype/src/ot.rs` at commit 6146e00.

1. Protocol model (editor, `OTServer`, two FIFO channels). State: server revisions and queue, editor buffer and revision counters, edits in flight to the daemon (`up`), messages in flight to the editor (`down`). Transitions: a CRDT change arrives, the editor types, the daemon receives an editor edit, the editor receives a daemon message (applied iff its revision equals the editor's edit count, else ignored, as `vscode-plugin/src/extension.ts` does).
   - `inv` is inductive (`lemma_init`, `lemma_crdt_step`, `lemma_ed_local`, `lemma_srv_recv`, `lemma_ed_recv`) over every interleaving of those four transitions (and only those: no editor rejection, open/close, or several editors).
   - `theorem_quiescent_agreement`: if nothing is in flight, editor buffer equals the daemon's `current_content` and the editor has applied every daemon op.
   - `example_run` is a concrete overtaking run that ends quiescent: it shows `inv` and the transitions are reachable, not that the OT axioms are meaningful (the identity model `ap(d,o)=d` also satisfies them, so the OT axioms are consistent but weak evidence of fit).
2. Refinement of the real `OTServer` code. Bodies of `apply_crdt_change`, `apply_editor_operation`, `deltas_for_editor`, `transform_through_operations` are the source bodies with the rewrites below. Verified:
   - `apply_crdt_change`: Err leaves state unchanged (its only caller, `EditorConnection::message_from_inside`, `.expect`s success, so an Err still crashes the daemon; the model's `crdt_step` assumes success, which is not proved); Ok equals the model's `srv_crdt` and sends the model's message.
   - `apply_editor_operation`: no panic and no overflow for any input revision, given the preconditions `editor_revision < usize::MAX` (and `daemon_revision < usize::MAX` for `apply_crdt_change`) and the trusted no-panic externals; every path (including both `bail!`s and the conversion error) keeps the server invariant `wf`; Ok equals the model's `srv_edit`, the CRDT receives the transformed op, the editor receives one delta per queued op, each with the new revision.
   - `transform_through_operations` equals the specification `tt`, including the base-length padding.
3. Negative controls (`negative/`), each rejected by Verus: protocol mutants (no transformation, no resend of the queue, editor ignores revisions) and code mutants (`code_skips_editor_revision_bump.rs`, `code_never_confirms.rs`). So the proof depends on the protocol's rules and on the real code's details.

## Trusted base (every assumption)

- Verus, Z3, rustc.
- `axiom_tp1`: the real crate's `transform` satisfies TP1, unconditionally on text. Not proved for the real crate (`../ot/REPORT.md`: bounded checks only).
- `axiom_pad`: appending `retain(n)` does not change `force_apply`'s result.
- External specs (not verified): `force_apply`/`apply` never panics; `transform` never fails; `try_from_delta(..).expect(..)` in `deltas_for_editor` never fails; `.into()` conversions between `OperationSeq`, `TextDelta`, `EditorTextDelta` preserve the denoted op (`ed_op`, `delta_op`); `drain`, `clone`, `retain`, `base_len`, `chars().count()` behave as specified.
- Editor model: an editor follows the plugin rules above and sends only edits that fit its buffer (Ok path). Not modeled, found by the reviewer in `extension.ts`:
  - the editor rejecting a daemon edit (`applyEdit` fails) and sending an empty delta with `editor += 1` (would need an identity op);
  - the "content unchanged" branch that bumps `daemon` without applying (same identity-op need);
  - a local change landing during `applyEdit`, which `processLocalEdit` may resend as an editor edit while `daemon` is not incremented (possible duplicate/misapplied edit; neither proved nor refuted);
  - open failure, close, reopen, several editors per document, the nvim/emacs plugins, and liveness (that quiescence is ever reached).
  A daemon-rejected edit ("Invalid edit", `editor_connection.rs`) leaves the editor having applied what the daemon did not, so the world invariant is lost; only the server's `wf` is proved to survive.
- `ed_op` ignores the buffer: the model assumes the conversion between editor (line/column) and text deltas means the same op whatever text it is given, which holds only if that text is the editor's buffer; nothing checks that.
- `ap` is total; the real `apply` panics if `base_len` exceeds the text length, and `apply_crdt_change`'s length check is not related to `ap` in the model. `operations` (history log) is outside the model.
- Nothing proves that a legitimate in-model editor edit returns Ok from `try_from_rev_ed_delta`; the model assumes success.
- Only the VS Code plugin's rules were read; the nvim and emacs plugins are not modeled.
- CRDT changes are arbitrary ops applied to `current_content`: the CRDT, its cache, and other peers are abstracted. That every peer's CRDT converges (Automerge) is assumed, not proved.
- Rewrites from source (checked by reading): `debug!`/`warn!` removed; `.into()` made named functions; `bail!(..)`, `.context(..)?` became `return Err`/`match`; `for` loops became index `while`; `(op_seq, self.editor_queue) = f(..)` split into `let` plus two assignments; fields `pub`; `Default` made explicit; `assert!` does not occur in the current source (earlier panics were already fixed in 4f83be7/e28f9e0).
- Not covered by Verus at all: `daemon.rs` (cache vs CRDT vs disk, Git deferral, watcher), `document.rs`, `editor_connection.rs`, `types.rs`. These were tested instead (below).

## Empirical race test for the unproved layers

`crates/teamtype/src/daemon_race_tests.rs` (commit 6146e00) drives 2 or 3 real `DocumentActor`s with temp directories, real sync messages in flight, simulated VS Code editors with in-flight edits, and random disk writes, removals, recreations and watcher events. At quiescence it checks: all CRDTs agree; each cache equals a fresh reload of the CRDT; disk equals the CRDT where no editor owns the file; editor buffers equal the CRDT. After every delivery it also checks cache == CRDT, which localized bug 2. Seeds: `RACE_SEEDS=n`, `RACE_SEED=k` (single run). Actor ids are random, so conflict winners vary run to run.

## Bugs found and fixed (commit 6146e00)

1. Recreated file deleted for everyone. `remove_disk_file` left a stale `disk_content` entry, so writing a recreated file read the missing disk file as a local deletion, deleted the file from the CRDT, and peers then recreated and deleted it in a loop (sync never settled). Fix: drop the entry on removal. Test: `recreated_file_is_not_deleted_by_peer_that_removed_it`.
2. Cache diverged from the CRDT on a concurrent create. When two peers recreate one path and a third learns of the loser first, Automerge reports `Conflict` plus the winner's text as edits at that path; the cache appended it ("xx" vs "x"), then wrote and sent the wrong text. Fix: `Document` reports a changed visible text object as a text `PutMap`, which the existing code turns into clear-then-fill. Test: `text_of_a_losing_concurrent_object_does_not_leak_into_cache` (a recorded failing document and sync message).

## Lessons

- Verus proves what the model says. The model's boundary (the editor model, the OT axioms, the abstract CRDT) is where bugs hide; the bugs here sat in the abstracted layer, found by running the real code under random interleavings.
- Random testing needs a checkable invariant after every step, not only at the end: that localized bug 2 from a 60-step trace to one delivery.
- Libraries report diffs, not states. Automerge's patch for a conflict flip looked like an edit of the old object; code that trusts patches as edits of what it already holds is fragile. Compare before and after state.
- Stale bookkeeping (a "last seen on disk" record) turns a later legitimate event into a spurious one. Every cache needs an invalidation rule for each way its source can change.
- The prior panics (`assert!` on editor revisions) were visible to the protocol proof as a failed precondition; moving to `return Err` made the proof need no precondition.
