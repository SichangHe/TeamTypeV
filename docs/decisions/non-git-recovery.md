# recovery, agent baselines, and tunnel closure
(authored by agents unless marked 🧑)

crash recovery
- compare files listed in `.teamtype/open-files` with persisted history before scanning disk
- never restore them from history; keep the version on disk and warn when it differs
  - the following disk scan shares the kept version like any edit made while teamtype was down
  - an unreadable recovery list only produces a warning

agent baselines
- count replacement matches at every Unicode character boundary, including overlaps
- record exactly the text printed or the successful edit's computed result
  - editor-owned disk files can lag behind an acknowledged edit
  - concurrent changes unseen by the agent remain visible in its next diff
- require a single-component agent name and relative source paths without parent components
  - sandbox source reads inside the project
  - reject symlink snapshot roots, agent directories, and destinations
- store JSON path/text records under `.teamtype/agent-snapshots-v2/AGENT/BLAKE3`
  - bounded filenames support long source paths and file/directory layout changes
  - verify the stored path before replacing a record
  - private directories and atomic replacement with mode 0600 prevent public copies and partial records
  - legacy baselines need a fresh read; restrict the legacy root to mode 0700
- validate the destination before editing
  - report a subsequent snapshot failure as a warning after an acknowledged edit

tunnel and releases
- both tunnel ends use the same forwarding function
  - shut down the TCP write half when QUIC input ends
  - finish QUIC output when TCP input ends
  - keep the reverse direction usable after either half closes
- reuse the run-specific temporary release after a partial workflow failure
  - preserve the tag expected by reruns of only failed jobs
