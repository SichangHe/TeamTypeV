# Daemon-owned editor saves
(authored by agents unless marked 🧑)

shared text has one writer: the daemon
- 🧑 "their save just tells teamtype to write"
- `daemonWriter` checks protocol support before an editor starts sharing
- `open.daemonWrites` opts into this contract
  - missing opt-in and legacy `savesFile: true` are rejected
  - update older plugins before sharing with the new daemon
- `save` only accepts files opened by the requesting connection
  - failed replacements return an error and leave the document actor available for retry
  - failed persistence prevents replacement and forces a full document save on retry
  - Git flushes propagate write errors before starting Git

editor buffers
- VS Code uses a `teamtype:` filesystem provider
  - protocol messages still use `file:` URIs
  - native saves call the daemon and preserve VS Code's saved/undo state
  - unshared files and non-UTF-8 files retain normal file buffers
  - native handoff preserves observed clean text as the base for unsaved edits
    - unknown dirty baselines stay read-only for explicit reconciliation
    - clean reloads refresh the base after preparation
  - local events received during a remote edit are buffered until its application result is known
- Emacs intercepts shared saves with `write-contents-functions`
  - a synchronous save request preserves save errors
  - backups, autosave files, and automatic disk reloads are disabled for shared buffers
  - disk timestamps never trigger native conflict prompts for shared buffers
  - disconnects leave shared saves blocked

outside changes
- the actor keeps the last disk bytes as the merge base
- watcher events, rescans, edits, and saves reconcile disk against that base
  - concurrent shared and outside deltas are transformed before application
  - outside deltas pass through each editor's existing OT state
  - binary replacements invalidate editor text state until a fresh open
- Linux and Apple replacements exchange a staged file with the destination atomically
  - displaced bytes are merged before a further write
    - includes binary replacements
  - delayed removal events recheck the path before deleting shared content
- platforms without atomic exchange reject writes
- an outside process retaining an old file descriptor across replacement is not coordinated
- crash recovery of a displaced temporary file is not implemented
- checkout can delete recently saved typing because its replacement is compared with the latest disk bytes
  - this implementation does not meet the no-lost-text acceptance requirement
- an external Git operation that unlinks before creating can race daemon recreation and fail with `File exists`

verification
- the VS Code suite also runs native Emacs with `TEAMTYPE_EMACS_BINARY`
- both editors exercise outside writes, Git checkout, Git pull, typing, and saves
- Rust regressions cover a disk edit before watcher delivery and concurrent unflushed shared text
