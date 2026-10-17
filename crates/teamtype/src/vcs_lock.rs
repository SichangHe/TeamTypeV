// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

// 🧑 "I was talking about edits basically whoever edits gets the lock ... It shouldn't be possible
// for two clients to both get the lock. ... Once there is a git commit happening, it should make it
// impossible to start another git commit even from another client and it should only die down
// after a timeout. We should say which user is holding the lock and tell them they need to ask
// that person"
//! The Git lock: one peer at a time may change version-control directories such as `.git`.
//!
//! Only the sharer grants the lock, so two peers never both hold it. A peer asks for the lock, and
//! keeps it, by being active: editing shared files or running Git commands that change branches
//! (through a `reference-transaction` hook that runs `teamtype git-lock`). The lock is released
//! after the holder is inactive for `timeout()`.
//!
//! The state lives in the shared document under `.teamtype/`, which is never written to disk:
//! - `GRANT`, written only by the sharer: who holds the lock.
//! - `WANT_PREFIX<peer>`, written only by that peer: a value that changes whenever the peer is
//!   active, so that every peer can time the peer's activity by its own clock.

use std::collections::HashMap;
use std::path::{Component, Path};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use tracing::info;

use crate::document::{Content, Document};
use crate::path::RelativePath;

pub const VCS_DIRS: [&str; 6] = [".git", ".bzr", ".hg", ".jj", ".pijul", ".svn"];
const GRANT: &str = ".teamtype/git-lock";
const WANT_PREFIX: &str = ".teamtype/git-want/";
/// Makes values invalid UTF-8, so that they are always stored as bytes.
const MAGIC: u8 = 0xFF;
/// The Git hook that asks for the lock. Each peer installs its own; it is not shared.
pub const HOOK: &str = ".git/hooks/reference-transaction";

/// `teamtype git-lock` asks the daemon for the lock by touching this file...
pub const REQUEST_FILE: &str = ".teamtype/git-lock-request";
/// ...and reads the answer from this one, written by `status_line`.
pub const STATUS_FILE: &str = ".teamtype/git-lock-status";

/// The lock is released after its holder is inactive for this long.
/// `TEAMTYPE_VCS_LOCK_SECONDS` overrides it, for tests.
#[must_use]
pub fn timeout() -> Duration {
    std::env::var("TEAMTYPE_VCS_LOCK_SECONDS")
        .ok()
        .and_then(|secs| secs.parse().ok())
        .map_or(Duration::from_mins(3), Duration::from_secs)
}

/// The version-control directory that `path` is in, if any.
#[must_use]
pub fn vcs_dir_of(path: &Path) -> Option<&'static str> {
    match path.components().next() {
        Some(Component::Normal(first)) => VCS_DIRS.into_iter().find(|dir| first == *dir),
        _ => None,
    }
}

/// Paths in the shared document that are never written to or read from disk.
#[must_use]
pub fn is_internal(path: &Path) -> bool {
    path.starts_with(".teamtype") || path == Path::new(HOOK)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Entry {
    peer: String,
    name: String,
    /// Milliseconds since the Unix epoch when written; only used to make every write distinct.
    nonce: u64,
}

impl Entry {
    fn encode(&self) -> Vec<u8> {
        let mut bytes = vec![MAGIC];
        bytes.extend(format!("{}\t{}\t{}", self.peer, self.nonce, self.name).bytes());
        bytes
    }

    fn decode(bytes: &[u8]) -> Option<Self> {
        let (&MAGIC, rest) = bytes.split_first()? else {
            return None;
        };
        let mut fields = std::str::from_utf8(rest).ok()?.splitn(3, '\t');
        Some(Self {
            peer: fields.next()?.to_owned(),
            nonce: fields.next()?.parse().ok()?,
            name: fields.next().unwrap_or_default().to_owned(),
        })
    }
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| u64::try_from(d.as_millis()).unwrap_or(u64::MAX))
}

fn read(doc: &Document, key: &str) -> Option<Entry> {
    match doc.current_file_content(&RelativePath::new(key)) {
        Some(Content::Bytes(bytes)) => Entry::decode(bytes),
        _ => None,
    }
}

/// Who holds the lock, as this peer sees it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Holder {
    Me,
    Other(String),
    Nobody,
}

#[derive(Debug)]
pub struct GitLock {
    peer: String,
    name: String,
    is_sharer: bool,
    timeout: Duration,
    /// When we last announced activity, and with which value.
    announced: Option<(Instant, u64)>,
    /// Each peer's last activity value, and when we first saw it.
    seen: HashMap<String, (u64, Instant)>,
    reported: Option<Holder>,
}

impl GitLock {
    #[must_use]
    pub fn new(peer: String, name: String, is_sharer: bool, timeout: Duration) -> Self {
        Self {
            peer,
            name,
            is_sharer,
            timeout,
            announced: None,
            seen: HashMap::default(),
            reported: None,
        }
    }

    #[must_use]
    pub fn peer(&self) -> &str {
        &self.peer
    }

    #[must_use]
    pub const fn is_sharer(&self) -> bool {
        self.is_sharer
    }

    /// Records activity, which keeps the lock or asks for it. Announcements are throttled unless
    /// `now`. Returns the announced value if the document changed.
    pub fn note_activity(&mut self, doc: &mut Document, now: bool) -> Option<u64> {
        if !now
            && self
                .announced
                .is_some_and(|(at, _)| at.elapsed() < self.timeout / 8)
        {
            return None;
        }
        // Strictly increasing, so that the sharer's confirmation can be compared with it.
        let nonce = now_ms().max(self.announced.map_or(0, |(_, nonce)| nonce + 1));
        self.announced = Some((Instant::now(), nonce));
        let want = Entry {
            peer: self.peer.clone(),
            name: self.name.clone(),
            nonce,
        };
        let key = format!("{WANT_PREFIX}{}", self.peer);
        doc.set_file(Content::Bytes(want.encode()), &RelativePath::new(&key));
        Some(nonce)
    }

    /// How long ago `peer` was last active, by our clock.
    fn idle_for(&mut self, doc: &Document, peer: &str) -> Option<Duration> {
        let want = read(doc, &format!("{WANT_PREFIX}{peer}"))?;
        let seen = self
            .seen
            .entry(peer.to_owned())
            .or_insert_with(|| (want.nonce, Instant::now()));
        if seen.0 != want.nonce {
            *seen = (want.nonce, Instant::now());
        }
        Some(seen.1.elapsed())
    }

    #[must_use]
    pub fn holder(&self, doc: &Document) -> Holder {
        match read(doc, GRANT) {
            Some(grant) if grant.peer == self.peer => Holder::Me,
            Some(grant) if !grant.peer.is_empty() => Holder::Other(grant.name),
            _ => Holder::Nobody,
        }
    }

    /// Whether the sharer has confirmed that we hold the lock as of our announcement `nonce`.
    /// The sharer decides one announcement at a time, so two peers are never both confirmed.
    #[must_use]
    pub fn confirmed(&self, doc: &Document, nonce: u64) -> bool {
        read(doc, GRANT).is_some_and(|grant| grant.peer == self.peer && grant.nonce >= nonce)
    }

    /// Updates timings and, at the sharer, moves and confirms the lock. Returns whether the
    /// document changed.
    pub fn tick(&mut self, doc: &mut Document) -> bool {
        let changed = self.is_sharer && self.decide(doc);
        let holder = self.holder(doc);
        if self.reported.as_ref() != Some(&holder) {
            match &holder {
                Holder::Me => info!("You hold the Git lock; other peers cannot change Git."),
                Holder::Other(name) => info!(
                    "{name} holds the Git lock; you cannot change Git until they are idle for {} seconds and you edit.",
                    self.timeout.as_secs()
                ),
                Holder::Nobody => {}
            }
            self.reported = Some(holder);
        }
        changed
    }

    // 🧑 "Let's not release the lock on a timeout. Let's make it so that always there is someone
    // holding the lock unless there's no one connected. And there can only be replacements in the
    // scenario when user A has the lock and has been idle and user B just started editing."
    /// At the sharer: the lock starts with the sharer and moves only from a holder idle for
    /// `self.timeout` to the peer that became active most recently. Confirms the holder's latest
    /// announcement.
    fn decide(&mut self, doc: &mut Document) -> bool {
        let peers: Vec<String> = doc
            .files()
            .iter()
            .filter_map(|path| {
                path.to_str()?
                    .strip_prefix(WANT_PREFIX)
                    .map(ToOwned::to_owned)
            })
            .collect();
        let mut idle: HashMap<String, Duration> = HashMap::default();
        for peer in peers {
            if let Some(duration) = self.idle_for(doc, &peer) {
                idle.insert(peer, duration);
            }
        }
        let grant = read(doc, GRANT);
        let mut holder = grant
            .as_ref()
            .map_or_else(|| self.peer.clone(), |grant| grant.peer.clone());
        let holder_idle = idle.get(&holder).copied().unwrap_or(Duration::MAX);
        if holder_idle >= self.timeout
            && let Some((next, _)) = idle
                .iter()
                .filter(|(peer, duration)| **peer != holder && **duration < self.timeout)
                .min_by_key(|(_, duration)| **duration)
        {
            holder.clone_from(next);
        }
        let want = read(doc, &format!("{WANT_PREFIX}{holder}"));
        let new_grant = Entry {
            name: want
                .as_ref()
                .map_or_else(|| self.name.clone(), |want| want.name.clone()),
            nonce: want.map_or(0, |want| want.nonce),
            peer: holder,
        };
        if grant.as_ref() == Some(&new_grant) {
            return false;
        }
        doc.set_file(
            Content::Bytes(new_grant.encode()),
            &RelativePath::new(GRANT),
        );
        true
    }
}

/// The daemon's answer to `teamtype git-lock`: who holds the lock, after handling the request
/// made at `request`.
#[must_use]
pub fn status_line(holder: &Holder, request: Option<SystemTime>) -> String {
    let request = request
        .and_then(|at| at.duration_since(UNIX_EPOCH).ok())
        .map_or(0, |d| d.as_nanos());
    match holder {
        Holder::Me => format!("me\t\t{request}\n"),
        Holder::Other(name) => format!("other\t{name}\t{request}\n"),
        Holder::Nobody => format!("nobody\t\t{request}\n"),
    }
}

/// Parses a `status_line`.
#[must_use]
pub fn parse_status(line: &str) -> Option<(Holder, u128)> {
    let mut fields = line.trim_end_matches('\n').splitn(3, '\t');
    let state = fields.next()?;
    let name = fields.next()?.to_owned();
    let request = fields.next()?.parse().ok()?;
    let holder = match state {
        "me" => Holder::Me,
        "other" => Holder::Other(name),
        _ => Holder::Nobody,
    };
    Some((holder, request))
}

/// The hook that makes Git ask for the lock before it changes a branch.
#[must_use]
pub fn hook_script(teamtype: &Path) -> String {
    format!(
        "#!/bin/sh\n\
         # Installed by teamtype: only the peer holding the Git lock may change branches.\n\
         [ \"$1\" = prepared ] || exit 0\n\
         exec '{}' git-lock\n",
        teamtype.display()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entry_round_trips_and_is_not_utf8() {
        let entry = Entry {
            peer: "abc".into(),
            name: "Ann B".into(),
            nonce: 42,
        };
        let bytes = entry.encode();
        assert!(String::from_utf8(bytes.clone()).is_err());
        assert_eq!(Entry::decode(&bytes), Some(entry));
        assert_eq!(Entry::decode(b"abc\t42\tAnn"), None);
    }

    #[test]
    fn paths_are_classified() {
        assert_eq!(vcs_dir_of(Path::new(".git/HEAD")), Some(".git"));
        assert_eq!(vcs_dir_of(Path::new("src/.git/HEAD")), None);
        assert!(is_internal(Path::new(".teamtype/git-lock")));
        assert!(is_internal(Path::new(HOOK)));
        assert!(!is_internal(Path::new(".git/HEAD")));
    }

    #[test]
    fn status_round_trips() {
        let line = status_line(&Holder::Other("Ann B".into()), Some(UNIX_EPOCH));
        assert_eq!(
            parse_status(&line),
            Some((Holder::Other("Ann B".into()), 0))
        );
    }

    #[test]
    fn the_lock_moves_only_from_an_idle_holder() {
        let mut doc = Document::default();
        let mut sharer = GitLock::new("s".into(), "Sam".into(), true, Duration::from_secs(1));
        let mut a = GitLock::new("a".into(), "Ann".into(), false, Duration::from_secs(1));
        let mut b = GitLock::new("b".into(), "Bob".into(), false, Duration::from_secs(1));
        sharer.tick(&mut doc);
        assert_eq!(a.holder(&doc), Holder::Other("Sam".into()));
        let nonce = a.note_activity(&mut doc, true).unwrap();
        sharer.tick(&mut doc);
        assert!(
            a.confirmed(&doc, nonce),
            "the idle sharer's lock moves to an active peer"
        );
        let nonce = b.note_activity(&mut doc, true).unwrap();
        sharer.tick(&mut doc);
        assert!(!b.confirmed(&doc, nonce), "an active holder keeps the lock");
        std::thread::sleep(Duration::from_millis(1100));
        sharer.tick(&mut doc);
        assert_eq!(
            b.holder(&doc),
            Holder::Other("Ann".into()),
            "an idle holder keeps the lock"
        );
        let nonce = b.note_activity(&mut doc, true).unwrap();
        sharer.tick(&mut doc);
        assert!(
            b.confirmed(&doc, nonce),
            "the lock moves from an idle holder to an active peer"
        );
        assert_eq!(a.holder(&doc), Holder::Other("Bob".into()));
    }
}
