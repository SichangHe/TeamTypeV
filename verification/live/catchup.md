# Catch-up regression checks
(authored by agents unless marked 🧑)

recovery
- `peer.rs`: heartbeat detects a stalled sync stream after six seconds without bytes
- first connects have a fifteen-second deadline; reconnects have an eight-second deadline
  - every third retry drops direct address hints and resets DNS while preserving known relay hints
  - other attempts reuse discovered addresses and do not reset discovery
  - attempts do not announce a network change
  - connection attempts run outside the endpoint actor so it can keep accepting handshakes
- the endpoint actor checks relay health every two seconds
  - Netwatch observes interface availability
  - make no endpoint replacements while all usable interfaces are down
  - restoration resets replacement backoff without bypassing the minimum endpoint age
    - pending outgoing dials may end when their disconnected endpoint is closed
    - pending incoming handshakes still prevent replacement
  - when no sync or tunnel task remains and no home relay is connected, bind a fresh endpoint with the same identity
  - this clears relay dialing backoff at the sharer as well as at joiners
  - wait at least fifteen seconds before the first replacement
  - double the interval after each attempt and stop replacements when the next interval exceeds five minutes
  - reset after a live connection or connected relay
  - incoming handshakes run concurrently with the health check
  - the health check has priority over queued reconnect attempts
  - defer replacement until incoming and outgoing handshakes finish or reach their deadlines
  - await endpoint closure for at most two seconds instead of spawning detached closers
- disable UDP segmentation offload to avoid the repeated post-outage stalls observed with slirp4netns

soak
- run `SOAK_BINARY=/path/to/teamtype python3 verification/live/soak.py --work /tmp/catchup-run --duration-s 3600 --joiners 4 --seed 619`
- each peer uses a separate network namespace with default discovery and public relays
- agent edits run every second on all peers; the sharer's real Neovim plugin edits every two seconds
- seeded faults rotate ten one-second link drops, a 30-second outage, and a 90-second outage
  - restoration also replaces the default route
- catch-up measures delivery to every peer file of all accepted markers present at restoration
  - editing continues during measurement
  - polling every 200 ms; observations must be under `--catchup-limit-s`, default 10 seconds
- quiescent checks require identical files, all accepted markers, no duplicates, and sharer editor agreement
- `events.jsonl` retains fault timing, accepted/rejected edits, recovery times, checks, and process identities
- the daemon log reader permits lines up to 8 MiB
  - full document debug messages can exceed Python's default 64 KiB limit and block daemon output
  - prefer `RUST_LOG=info,teamtype::peer=debug,iroh=debug` for network diagnosis
- cleanup terminates only the harness's own process groups

long outages
- run `TEAMTYPE_BINARY=/path/to/teamtype python3 verification/live/sleep.py --modes network --durations 30 120 600 --repeats 2 --workers 2 --work /tmp/catchup-long`
- the recovered sleep harness uses a sharer and two joiners, each with real Neovim
  - one joiner's interface is dropped; the other peers keep editing
  - includes an edit just before disconnection and an offline edit
- recovery requires exact file and editor-buffer agreement with all expected lines once
  - after recovery, further edits from every peer must converge
  - a recovery of ten seconds or longer fails
- `--modes sleep` instead pauses a daemon and its editor with SIGSTOP
- results and expected lines remain in the selected evidence directory

relay regressions
- run `SOAK_BINARY=/path/to/teamtype python3 -m verification.live.slow_relay /tmp/new-slow-relay-evidence` from the repository root
  - proxy relay upgrades to the public west-coast relay with a five-second delay
  - health probes pass immediately so relay selection can finish
  - run a thirty-second sharer outage with two joiners and concurrent edits
  - record latency and require convergence within the harness's existing two-minute timeout
  - the ten-second assertion applies to the ordinary hour-long soaks
- workspace tests include a direct tunnel with an unreachable relay
  - forwarding must remain usable after seventeen seconds without any sync peers
- run the long-outage command with `--durations 1800 --repeats 1 --workers 1` for a fully offline thirty-minute peer
  - count `Refreshing the disconnected relay endpoint.` in that peer's log

limits
- simulated interface outages keep the IP address and slirp process
- successful runs establish measured recovery times in this environment, not a bound for arbitrary networks
- these checks exercise insertions in one shared file
- the soak measures file catch-up; editor agreement is checked at quiescence
- endpoint replacement stops after five consecutive attempts during extended outages
  - Iroh continues its own relay retry loop on the retained endpoint
- one healthy peer or tunnel keeps the endpoint alive during a partial outage
  - stalled peers retry independently and periodically omit direct address hints

acceptance
- `bash verification/live/catchup_checks.sh` builds the debug binary needed by the editor tests, then runs the workspace tests, clippy, and both required live scripts sequentially
- `CATCHUP_CHECK_LOG_DIR` selects retained logs; successful checks print nothing
