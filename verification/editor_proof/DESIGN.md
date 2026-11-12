# Editor protocol proof: rejection, many editors, reopen, liveness
(authored by agents unless marked 🧑)

Extends `../concurrency/` (single editor, no rejection). `editor_protocol.rs` = the old proof (unchanged, `base_part.txt`) plus two parts; `./check.sh` assembles and runs it: 54 verified, 0 errors; three mutants in `negative/` are rejected.

## Proved (fact: Verus-checked, under the trusted base below)

1. Validity. Every op fits the text it is applied to (`vseq`), so the daemon's `apply_editor_operation` and `apply_crdt_change` never see an unfitting op, and a correct editor never has to reject a daemon edit (`lemma_ed_recv_v`: an accepted message fits the buffer).
2. Editor rejection (`ed_reject`, `lemma_reject`). If the editor rejects a daemon edit and sends an empty delta with `revision = daemon_rev` and `editor_rev += 1` (the VS Code rule), `inv` and validity are preserved, so the daemon edit is later re-delivered transformed and the editor still converges. Mutants: sending nothing, or not bumping `editor_rev`, fail.
3. Many editors per document. `G` has one session `W` per editor and the daemon CRDT as hub. An editor's edit is transformed by its server, applied to the CRDT, and broadcast to all other servers (as `process_component_message` and `broadcast_to_editors` do); outside changes go to all servers. `ginv`: every open session satisfies `inv` and `vinv`, and its server's `current_content` equals the CRDT text. Mutant without broadcast fails.
4. Open, close, reopen, disconnect. `g_open` (with an arbitrary buffer; the daemon sends `diff(buffer, crdt)` as a first daemon op, as `ComponentMessage::Open` does) and `g_close` keep `ginv`.
5. Agreement: `theorem_agreement`: if no session has anything in flight, every open editor's buffer equals the CRDT.
6. Liveness: `theorem_liveness`: for every scheduler that never idles while something is in flight (fair delivery; `lemma_fair_exists` shows one exists), delivery reaches quiescence in finitely many steps and then all open editors match the daemon. Measure: (inputs, rejections, edits up, messages down), lexicographic. Rejections are budgeted (`rej`): unbounded rejection would break termination, and the real plugin only rejects when `applyEdit` fails.

## Trusted base (assumptions, not proved)

- Everything in `../concurrency/DESIGN.md`: OT axioms (TP1, padding), external specs, the editor follows the plugin rules.
- New axioms: `axiom_id` (empty delta is identity), `axiom_diff` (the diff op turns a into b), `axiom_transform_fits` (the OT crate's transform of two ops that fit one text yields ops that fit the other result). `fits` is abstract: that real `try_from_rev_ed_delta`/positions mean the same as `fits` is assumed.
- The daemon layer: while any editor has the file open, the CRDT keeps the file text (peer deletion handled in `daemon.rs` `FileRemoval`); each actor step is atomic; inputs after quiescence are modeled as a budget, so liveness is "after inputs stop".
- Session freshness. Model: a reopened editor's old in-flight messages are gone. Real protocol has no session id; old daemon messages with a matching revision could be accepted by a new session. Reported to the plugin reviews (see their docs); not provable until the plugin drops them.
- Plugins: only their abstract rules are modeled here. See `vscode/` and `nvim_emacs/` for the plugin-side checks.
- Not modeled: Git deferral, persistence, cursors, CRDT convergence between peers, daemon crash.
