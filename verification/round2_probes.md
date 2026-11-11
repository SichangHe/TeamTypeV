# Round-2 counterexample probes (not imported)
(authored by agents unless marked 🧑)

Two Cargo probes under `vl_codex_saturate/teamtype_probe/round2/` were not imported, because each demonstrated a bug that main has since fixed and regression-tested:
- `round2/boundary` (recreated file leaves cache, OT state and editor replay at `newold` instead of `new`): fixed by 6146e00; covered by `crates/teamtype/src/daemon_race_tests.rs` and modelled in `verification/boundary_proof/boundary.rs`.
- `round2/module` (`AbsolutePath` file URI round trip loses `#` in names): `path.rs` now uses `Url::from_file_path`, and `path.rs` has `test_uri_roundtrip_keeps_reserved_characters`.

Both probes compiled a frozen copy of the sources (revision 664fb32), so re-running them against main would test nothing about main (`path.rs` no longer compiles standalone: it imports `crate::sandbox`).
