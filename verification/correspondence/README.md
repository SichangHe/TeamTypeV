# Mechanical proof/source correspondence
(authored by agents unless marked 🧑)

Status: fallback mechanism (extractor + reviewed golden diffs) works for `concurrency/`. In-place verification of real files is not done (see end).

## Idea
A proof copy may differ from repo code only by rewrites a human reviewed. `corr.py` extracts each marked item from the real repo file, diffs it against the proof copy (comments, blank lines, indentation ignored), and compares that diff with a stored golden diff. Any change in the repo item or in the proof copy changes the diff, so the check fails until someone re-reviews it. A proof using a stale copy cannot pass.

## How to adopt (3 steps)
1. In your proof `.rs`, wrap each copied item:
   ```
   // corr: crates/teamtype/src/ot.rs :: OTServer::apply_crdt_change
   pub fn apply_crdt_change(...) -> (r: ...) requires ... { ...body... }
   // corr-end
   ```
   Selector forms: `name` (free fn, must be unique in file), `Type::name` (method in an `impl ... Type`), `struct X`, `enum X`, `type X`, `trait X`, `const X`, `impl X` (whole block). Attributes/doc comments directly above are included. Exactly one match is required.
2. Add your proof path (relative to this dir) to `proofs.txt` (marker check) and `verus_targets.txt` (Verus run; optional extra flags after the path, e.g. `foo.rs --crate-type=lib`).
3. `python3 corr.py update` writes `golden/*.diff`; READ every new diff: it must contain only Verus specs/ghost code and mechanical rewrites (`.into()` to named fn, `bail!` to `return Err`, loops to `while`). Anything that changes behavior is a bug in the proof. Commit the golden files. Then `./run_all.sh [repo]`.

Rules
- Copy the repo body, not a paraphrase; keep rewrites minimal so diffs stay reviewable.
- Do not mark items you rewrote heavily or wrote from scratch (models, specs); those are trusted and belong in your trusted-base list.
- Unmarked code is NOT checked. Coverage = marked items.
- Re-run `update` after any intended repo change, and re-review the golden diff in the commit.

Commands
- `python3 corr.py check [--repo DIR] [--proofs F...]` fails on: drift, missing golden, orphan golden, 0 or >1 selector matches.
- `SKIP_VERUS=1 ./run_all.sh` marker check only (cheap).
- `./run_all.sh` marker check, then Verus on each target; requires >=60 GiB MemAvailable.

CI
- `.github/workflows/proofs.yml`: runs the cheap correspondence job on every push and PR (python only). The Verus job is disabled (`if: false`) until a self-hosted runner with ~60 GiB exists. Proof copies live under `verification/`.

## Limits (honest)
- Textual, not semantic: golden diffs are only as good as the review. A spec-only edit in a proof also changes the diff and needs re-review (intended, noisy).
- Callees are trusted via `external_body` specs; those are not checked by this tool.
- Selector uses a comment/string-aware brace matcher, not a Rust parser; macros with unbalanced braces in strings are masked, but exotic syntax may mis-extract (then the diff shows it).
- Verified end-to-end drift test: changing `daemon_revision += 1` to `+= 2` in a copy of `ot.rs` fails `check`.

## Not done: in-place verification
Preferred option (Verus annotations inside real sources) needs the repo to depend on `vstd`/builtin macros behind a feature and refactoring for Verus-friendly code; not attempted.
