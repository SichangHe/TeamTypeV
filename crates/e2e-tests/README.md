<!--
SPDX-FileCopyrightText: 2024 Danny McClanahan <dmcC2@hypnicjerk.ai>
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

This directory contains end-to-end integration tests for TeamTypeV.
They assume that your `PATH` contains:

- An `nvim` with installed TeamTypeV plugin, and
- a `teamtype` binary (for connecting via `teamtype client`).

To run all e2e tests except the fuzzer, run:

```bash
cargo test
```

To run specifically the fuzzer, run:

```bash
cargo test --test fuzzer
```

<!-- authored by agents -->
After `cargo build -p teamtype`, the real-daemon regression tests also run from the repository root:

```bash
bash verification/live/git_forward.sh
bash verification/live/git_forward_regressions.sh
CASE=portable bash verification/live/git_forward_regressions.sh
bash verification/live/people.sh
bash verification/live/history.sh
```

The Git test checks forwarding from joiners without `.git`, immediate-edit commits, checkout with files closed in editors, stdin and binary output, command serialization, and disconnection. See [Git forwarding](../../docs/git-forwarding.md).
