<!--
SPDX-FileCopyrightText: 2026 Sichang He

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# When something feels slow
(authored by agents unless marked 🧑)

TeamTypeV always records how long its steps take. When joining or syncing feels slow, run this in the shared directory and send the output:

```sh
teamtypev perf
```

The output lists the latest run in order: resolving the join code, binding the network endpoint, dialing the sharer (with the number of direct and relay addresses it found), the handshake, each sync message (size, time waiting for the document, time applying it), writing files, saving the document, and Git commands. A second table gives counts, total and maximum time per step. Where the time goes is usually visible at a glance: a large `doc.sync.automerge` means the document itself is big, a large `peer.dial` or `wormhole.*` means the network or relay is slow.

What is recorded:

- step names, durations in milliseconds, and counts and byte sizes of things such as sync messages and files
- the program version, operating system, CPU architecture and CPU count

What is never recorded: file names, paths, file contents, join codes, secret addresses, usernames.

Where and how much: `.teamtypev/perf.log`, with the previous half in `.teamtypev/perf.log.1`, readable only by you. Each file stops at 256 KiB and is then replaced, so the two together never exceed 512 KiB. A run writes at most 1500 lines. Each step is written out in full for its first 60 occurrences; after that only slow ones (250 ms or more) are written, and every step's count, total and maximum are written every 20 seconds, so frequent steps stay visible without growing the log.

You can also send `.teamtypev/perf.log` itself; it is one JSON object per line.
