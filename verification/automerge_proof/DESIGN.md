# CRDT data-layer proofs (map + text)
(authored by agents unless marked 🧑)

Run each file with Verus (see `../correspondence/verus_targets.txt`). Source read: automerge 0.10.0 from crates.io; it is not vendored because no proof needs to modify it.

## Proved
- `crdt_map.rs` (11 verified, 0 errors): the `files`-map register layer with incremental apply.
  - state = opid -> (op, succ set); `apply` inserts the op and adds its id to each pred's succ; an op is visible iff succ is empty; delete = op without value.
  - `theorem_run_is_canon`: any causally valid history (ids distinct, preds delivered earlier) yields exactly the order-free canonical state of its op set.
  - `theorem_sec_map`: two valid histories of the same op set give equal states; `corollary_visible_equal`: equal visible sets and equal conflict winner (greatest id).
  - `example_run`: concurrent puts (conflict, winner = greater id) and a delete, three delivery orders, concrete reads.
- `crdt_text.rs` (14 verified, 0 errors): RGA sequence with a one-op model of the insertion rule in `batch.rs untangle_inserts` (not a refinement of it).
  - `ins` = scan after the reference element, skipping elements with greater id, insert before the first smaller (see REAL comments in the file).
  - `lemma_ins_preserves`: the scan keeps the invariant "each element follows its reference and every element between has a greater id".
  - `lemma_unique`: two lists with that invariant over the same elements are equal (remove the max-id element; it has no referrers because ids exceed their reference's id, and it sits directly after its reference).
  - `theorem_sec_text`: two causally valid histories (inserts and deletes) of the same op set give equal lists, equal deleted sets, equal visible text. `example_run`: concurrent inserts where the scan skips, plus a delete.
- Negative controls (`negative/`, each rejected): map without succ update, map succ overwrite; text without skip, skipping smaller ids, inserting before the reference.

## Trusted base / not proved
- Verus, Z3, rustc.
- Model fidelity is by reading, not refinement: the real code is the columnar batch applier (`op_set2/change/batch.rs`, `Untangler`, `walk_list`) and `op_set.rs add_succ`. My `apply`/`ins` are the one-op specialisation of that rule; I did not verify the columnar encoding, the skip-list/indexes, or that batch application of several changes equals sequential application.
- Causal delivery: assumed that Automerge applies a change only when all its dependency changes are applied (its queue, `automerge.rs get_missing_deps`/`queue`), and that op preds/references/ids obey the model's `valid` (preds delivered earlier; Lamport: id > reference/pred id; ids unique). Real Lamport counters are `max_op+1` (not verified here).
- Change hashing/dedup, actor-index remapping, change encoding/decoding, `load`/`save`: not modelled.
- Scope: map registers and list/text insert/delete only. Not modelled: counters, marks, make-object nesting (objects are independent: `key` stands for (object, key)), list element overwrite (put on a list index), and that a text element's single `ch` is one Unicode scalar / the encoding index conversion (TextEncoding).
- Object-level conflict winners over make-object ops follow from the map theorem (state equal), but which text object `text_obj` reads is not modelled.
- Not done: patch fidelity (`types.rs PatchEffect::try_from` vs before/after states, `document.rs replaced_text_objects_as_puts`). No bug was found or claimed in this part.
- Vstd note: this vstd's `Set::new` returns `Option`; the files use `ISet`/`IMap`.

## Batch insertion (`crdt_batch.rs`, 39 verified, 0 errors; negatives in `negative/batch_*.rs`)
- Model: `batch_ins(list, ops)` = `walk_list` + `Untangler` (batch.rs:28-330). `stack` starts as the HEAD ops; at each doc element d: `drain` pops down to `n` (the `while stack.len() > n` loop; each pop emits the op and pushes its children = `gosub`), then pushes `entry[d.id]` (= `kids(ops, Some(d.id))`), then d is emitted; at the end `drain(.., 0)` (= `finish_inserts`). `n = pp(stack, d.id)` models `binary_search_by(..).Err(n)`.
- Proved: `lemma_batch_facts` (result satisfies `inv`, has exactly list+ops elements), `theorem_batch_eq_seq` (= sequential `ins` fold in ANY causal order of the same ops), `corollary_order_independent`, `lemma_ops_causal`/`corollary_batch_eq_idsorted` (the id-sorted batch is itself a causal order). The stack is kept strictly ascending (`asc` in `stack_inv`; proved, `lemma_drain`/`lemma_walk`); `lemma_pp` shows `pp` is the correct binary-search result on an ascending stack.
- Proof shape: invariant over (out, stack, dp): out satisfies the RGA `inv` (prefix-closed), every stack op satisfies `cond` (its reference is in out and everything after it is greater), every batch op in out is followed by a smaller doc element (`winv`); completeness by a min-id argument (`lemma_min_unplaced`) over `jinv`.
- Assumptions (`valid_ops`): `inv(list)`; ops ids unique and not in list; Lamport (ref id < op id); every reference is in list or in ops; ops sorted ascending by id (`sorted_ops`).
- The sortedness assumption holds in the real code by a separate step, not by `Untangler`: `order_ops_for_doc` (batch.rs:919) sorts change_ops by (obj, elemid_or_key, id) and for an insert op `elemid_or_key` is its OWN id (op_set2/op.rs:144-146), so inserts are ascending by id. `Untangler::new` and the entry/gosub pushes rely on it: without it the stack is not ascending and `binary_search` is meaningless. Concrete failure if it did not hold: `negative/batch_unsorted_counterexample.rs` (ops [5@b, 3@a] after HEAD give [3,5]; RGA gives [5,3]). Reading says the sort makes this unreachable; no bug claimed.
- Differential test (not a proof): `explore/batch_diff` (scratch crate kept outside the repo, unmodified automerge 0.10.0) - 30000 random runs of 2-4 actors with concurrent splice/delete edits on a non-empty text, partial syncs; all changes applied via `apply_changes` as one batch (original and shuffled order) and one at a time vs sequential `merge`: 0 mismatches.
- Not covered: deletes/succ (`pred` handling) and update ops (`element_update`/`updates_stack`), marks, overwrites of list elements; per-op `subsort`/`pos` columns and the final `sort_by` (the model takes the emission order of the stack machine as the result order); `top`/visibility index; actor-index ordering (ids are abstract totally ordered pairs); `drain` has a termination guard (top is an unplaced batch op) that the proof shows always holds; the real `assert!(entry.is_empty())` panics if a reference is missing (model assumes it is present); how apply_changes_batch orders/queues changes before this step is not modelled.

## Sync convergence: how the pieces compose
Goal: after edits stop and the network delivers, every peer's shared directory holds the same files.
1. Delivery: `../liveness_proof/teamtype_peers.rs` Part A shows that, if each sync connection keeps generating and receiving messages, every change reaches every connected peer. It assumes the sync protocol's per-edge behaviour (`gen` sends what the sender believes the receiver lacks; `rcv` delivers it). That assumption stands for Automerge's `generate_sync_message`/`receive_sync_message` and is not proved here.
2. Same change set gives the same document: `crdt_map.rs` (map registers), `crdt_text.rs` and `crdt_batch.rs`/`crdt_batch_full.rs` (text, batched application) show that any causal delivery order of the same operations gives the same state. Models are read against automerge 0.10.0, not refined from it.
3. Document to cache and editors: `patch_fidelity.rs` and `../boundary_proof/boundary.rs` show TeamType's cache and the editor deltas follow the document, given the patch contract in `PATCH_DESIGN.md` (trusted, tested by `document.rs` replay tests).
4. Document to disk and editors at quiescence: `../daemon_proof/disk_full.rs` (`theorem_idle_agreement`) and `daemon_proof.rs` (`theorem_quiescent_agreement_m`).

Not covered: Automerge's sync message encoding and its have/need/bloom-filter logic, change hashing and dedup, `load`/`save`, counters and marks beyond what `crdt_batch_full.rs` models, and liveness under message loss (connections reconnect; the model has reliable FIFO edges).
