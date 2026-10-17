// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

// 🧑 "for the concurrent commit you just forbid the user on the client side to commit and only
// have one major owner be able to commit. Maybe you produce a lock such that whoever starts
// editing gains that lock and be able to commit and everyone else cannot touch any git stuff and
// there is a timeout when they don't do anything for a while."
//! One peer at a time may change version-control directories such as `.git`.
//!
//! The lock is a binary file `<vcs dir>/teamtype-lock` in the shared document. A binary value has
//! no merge: when two peers take the lock at once, every peer ends up with the same single winner.
//! A peer takes the lock when it changes a file in a version-control directory while nobody else
//! holds it, and keeps it while it keeps changing such files. Other peers have their
//! version-control directories made read-only, so their Git commands fail instead of diverging.
//!
//! This is best effort: two peers that change version control before either sees the other's
//! lock both get their changes in, and the lock goes to one of them afterwards. The owner
//! (including root) can ignore directory permissions.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Component, Path};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use tracing::warn;

use crate::path::RelativePath;

pub const VCS_DIRS: [&str; 6] = [".git", ".bzr", ".hg", ".jj", ".pijul", ".svn"];
const LOCK_FILE_NAME: &str = "teamtype-lock";
/// The lock is released after this long without changes by its holder.
/// `TEAMTYPE_VCS_LOCK_SECONDS` overrides it, for tests.
#[must_use]
pub fn timeout() -> Duration {
    std::env::var("TEAMTYPE_VCS_LOCK_SECONDS")
        .ok()
        .and_then(|secs| secs.parse().ok())
        .map_or(Duration::from_mins(3), Duration::from_secs)
}
/// Makes the lock file's content invalid UTF-8, so that it is always stored as bytes.
const MAGIC: u8 = 0xFF;

/// The version-control directory that `path` is in, if any.
#[must_use]
pub fn vcs_dir_of(path: &Path) -> Option<&'static str> {
    match path.components().next() {
        Some(Component::Normal(first)) => VCS_DIRS.into_iter().find(|dir| first == *dir),
        _ => None,
    }
}

#[must_use]
pub fn is_lock_file(path: &Path) -> bool {
    vcs_dir_of(path).is_some()
        && path.components().count() == 2
        && path.file_name().is_some_and(|name| name == LOCK_FILE_NAME)
}

pub fn lock_file(vcs_dir: &str) -> RelativePath {
    RelativePath::new(&format!("{vcs_dir}/{LOCK_FILE_NAME}"))
}

#[must_use]
pub fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lock {
    /// The holder's peer ID.
    pub holder: String,
    /// The holder's username, for messages.
    pub name: String,
    /// When the holder took or renewed the lock, in milliseconds since the Unix epoch by the
    /// holder's clock. Only used to tell renewals apart; peers time the lock by their own clocks.
    pub taken_ms: u64,
}

impl Lock {
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = vec![MAGIC];
        bytes.extend(format!("{}\t{}\t{}\n", self.holder, self.taken_ms, self.name).bytes());
        bytes
    }

    #[must_use]
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        let (&MAGIC, rest) = bytes.split_first()? else {
            return None;
        };
        let text = std::str::from_utf8(rest).ok()?.trim_end_matches('\n');
        let mut fields = text.splitn(3, '\t');
        Some(Self {
            holder: fields.next()?.to_owned(),
            taken_ms: fields.next()?.parse().ok()?,
            name: fields.next().unwrap_or_default().to_owned(),
        })
    }
}

/// Adds or removes the owner's write permission on `dir` and every directory below it. Without
/// it, nothing can be created, renamed, or removed in a directory, which covers how Git writes.
pub fn set_dirs_writable(dir: &Path, writable: bool) {
    let Ok(metadata) = fs::symlink_metadata(dir) else {
        return;
    };
    if !metadata.is_dir() {
        return;
    }
    // A writable directory is needed to list and change its children only when making it
    // read-only, so change the order accordingly.
    if writable {
        set_dir_writable(dir, metadata.permissions().mode(), true);
    }
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            set_dirs_writable(&entry.path(), writable);
        }
    }
    if !writable {
        set_dir_writable(dir, metadata.permissions().mode(), false);
    }
}

pub fn set_dir_writable(dir: &Path, mode: u32, writable: bool) {
    let new_mode = if writable {
        mode | 0o200
    } else {
        mode & !0o200
    };
    if new_mode != mode
        && let Err(err) = fs::set_permissions(dir, fs::Permissions::from_mode(new_mode))
    {
        warn!("Failed to change permissions of {}: {err}", dir.display());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lock_round_trips_and_is_not_utf8() {
        let lock = Lock {
            holder: "abc".into(),
            name: "Ann B".into(),
            taken_ms: 42,
        };
        let bytes = lock.encode();
        assert!(String::from_utf8(bytes.clone()).is_err());
        assert_eq!(Lock::decode(&bytes), Some(lock));
        assert_eq!(Lock::decode(b"abc\t42\tAnn"), None);
    }

    #[test]
    fn paths_are_classified() {
        assert_eq!(vcs_dir_of(Path::new(".git/HEAD")), Some(".git"));
        assert_eq!(vcs_dir_of(Path::new("src/.git/HEAD")), None);
        assert!(is_lock_file(Path::new(".git/teamtype-lock")));
        assert!(!is_lock_file(Path::new(".git/refs/teamtype-lock")));
    }

    #[test]
    fn dirs_become_read_only_and_back() {
        let dir = tempfile::tempdir().unwrap();
        let sub = dir.path().join(".git/refs");
        fs::create_dir_all(&sub).unwrap();
        set_dirs_writable(&dir.path().join(".git"), false);
        assert!(fs::write(sub.join("x"), "x").is_err());
        set_dirs_writable(&dir.path().join(".git"), true);
        fs::write(sub.join("x"), "x").unwrap();
    }
}
