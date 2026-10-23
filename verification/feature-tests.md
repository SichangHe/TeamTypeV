# fork feature tests
(authored by agents unless marked 🧑)

commands
- `cargo build --profile test`
  - existing Neovim tests require `target/debug/teamtype` and Neovim
- `cargo test --workspace`
- `cargo clippy --all-targets`
- `cargo fmt --all -- --check`
- `python3 verification/test_install.py`
  - see [installer tests](install-tests.md)
- `python3 verification/test_nightly.py`
  - execute the workflow's release-creation shell against local release state twice
- `verification/live/people.sh` and `verification/live/history.sh`

coverage
- peer and sync tests use loopback Iroh endpoints without discovery or relays
  - heartbeats, stalled frames, reconnects, and progressing slow frames
  - subprocess history refusals preserve working files
- join tests pipe real confirmation answers to subprocesses
- socket tests check permissions, special bits, ancestors, and errors
- agent tests use CLI subprocesses, a protocol peer, and a real document actor
  - Unicode edits, overlapping matches, rejected edits, independent baselines, and diff filters
  - blocked stdout while disk changes and an editor that owns saving
  - path rejection, file/directory changes, long paths, and private snapshot modes
  - persisted open-file recovery refuses newer offline saves
- tunnel tests use loopback Iroh and TCP streams
  - authentication, binary forwarding, independent streams, and EOF in both directions
  - the reconnect branch of the guest listener remains outside these tests

design
- [recovery and baselines](../docs/decisions/non-git-recovery.md)
