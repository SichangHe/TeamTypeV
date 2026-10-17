// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

// 🧑 "Dropping the Git directory from history is worth it."
//! Version-control files travel outside the shared document, so they leave no history.
//!
//! Only the Git lock's holder changes them, so no merging is needed: the holder sends each changed
//! file, the sharer relays it to everyone else, and every peer writes what it receives. A peer
//! that connects to the sharer gets a full snapshot of the sharer's files first.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use serde::{Deserialize, Serialize};

/// A file's path relative to the shared directory, and its content, or `None` if removed.
pub type VcsFile = (String, Option<Vec<u8>>);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VcsMessage {
    /// Files changed by the peer `origin`.
    Changes { origin: String, files: Vec<VcsFile> },
    /// Part of the sharer's full set of files; the receiver removes its other files after the
    /// `last` part.
    Snapshot { files: Vec<VcsFile>, last: bool },
}

/// Snapshot messages are split at about this many bytes of content.
const SNAPSHOT_PART_BYTES: usize = 4 << 20;

#[must_use]
pub fn hash(bytes: &[u8]) -> u64 {
    let mut hasher = DefaultHasher::new();
    bytes.hash(&mut hasher);
    hasher.finish()
}

/// Splits `files` into snapshot messages; there is always at least one, the last.
#[must_use]
pub fn snapshot_messages(files: Vec<VcsFile>) -> Vec<VcsMessage> {
    let mut messages = vec![];
    let mut part = vec![];
    let mut part_bytes = 0;
    for file in files {
        part_bytes += file.1.as_ref().map_or(0, Vec::len);
        part.push(file);
        if part_bytes >= SNAPSHOT_PART_BYTES {
            messages.push(VcsMessage::Snapshot {
                files: std::mem::take(&mut part),
                last: false,
            });
            part_bytes = 0;
        }
    }
    messages.push(VcsMessage::Snapshot {
        files: part,
        last: true,
    });
    messages
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn snapshot_ends_with_last_part() {
        let big = vec![0; SNAPSHOT_PART_BYTES];
        let messages = snapshot_messages(vec![("a".into(), Some(big)), ("b".into(), None)]);
        assert!(matches!(
            messages.as_slice(),
            [
                VcsMessage::Snapshot { last: false, .. },
                VcsMessage::Snapshot { last: true, .. }
            ]
        ));
        assert!(matches!(
            snapshot_messages(vec![]).as_slice(),
            [VcsMessage::Snapshot { last: true, .. }]
        ));
    }
}
