// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

//! Always-on timing records, so that a log sent later shows where time went.
//!
//! Records go to `.teamtypev/perf.log` (and its previous half `perf.log.1`), one JSON object per
//! line. The two files together never exceed about 512 KiB: a file is replaced by a fresh one
//! when it reaches 256 KiB, and a session records at most [`SESSION_LINE_CAP`] lines. Each span
//! name is written in full for its first [`FULL_RECORDS_PER_NAME`] occurrences; later ones are
//! only counted, and written individually only when they are slow. Counts, total and maximum
//! durations of every name are written as `agg` lines every few seconds, so the cost of frequent
//! operations stays visible without filling the disk.
//!
//! Records hold names, durations and numbers only. Fields are `&'static str` names with `u64`
//! values, so file names, paths, secret addresses and text cannot end up in the log.
//!
//! `teamtypev perf` prints a summary of the latest session for pasting into a message.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};

use crate::sandbox;

/// A log file is replaced by a new one when it reaches this size.
pub const MAX_FILE_BYTES: u64 = 256 * 1024;
/// A session writes at most this many lines (aggregates included).
pub const SESSION_LINE_CAP: usize = 1500;
/// Occurrences of one name written in full before only slow ones are.
pub const FULL_RECORDS_PER_NAME: u64 = 60;
/// Later occurrences of a name are written individually when they take at least this long.
pub const SLOW: Duration = Duration::from_millis(250);
const AGGREGATE_EVERY: Duration = Duration::from_secs(20);

#[derive(Default, Clone, Copy)]
struct Stat {
    count: u64,
    total_ms: u64,
    max_ms: u64,
    last_up_ms: u64,
    reported_count: u64,
}

/// One log destination and the state of one session writing to it.
pub struct Perf {
    base: PathBuf,
    log: PathBuf,
    previous: PathBuf,
    session: String,
    start: Instant,
    size: u64,
    lines: usize,
    stats: BTreeMap<&'static str, Stat>,
    last_aggregate: Instant,
}

impl Perf {
    /// Opens the log under `base/.teamtypev` and writes the session header.
    pub fn open(base: &Path) -> Self {
        let log = base.join(".teamtypev/perf.log");
        let previous = base.join(".teamtypev/perf.log.1");
        let size = std::fs::metadata(&log).map_or(0, |metadata| metadata.len());
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |since| since.subsec_nanos());
        let mut perf = Self {
            base: base.to_path_buf(),
            log,
            previous,
            session: format!("{:04x}", (nanos ^ std::process::id()) & 0xffff),
            start: Instant::now(),
            size,
            lines: 0,
            stats: BTreeMap::new(),
            last_aggregate: Instant::now(),
        };
        perf.write(&json!({
            "ev": "session",
            "version": env!("CARGO_PKG_VERSION"),
            "os": std::env::consts::OS,
            "arch": std::env::consts::ARCH,
            "cpus": std::thread::available_parallelism().map_or(0, std::num::NonZero::get),
        }));
        perf
    }

    /// Records one finished operation of `name` that took `took`.
    pub fn span(
        &mut self,
        name: &'static str,
        took: Duration,
        note: &'static str,
        fields: &[(&'static str, u64)],
    ) {
        let ms = u64::try_from(took.as_millis()).unwrap_or(u64::MAX);
        let up_ms = self.up_ms();
        let stat = self.stats.entry(name).or_default();
        stat.count += 1;
        stat.total_ms = stat.total_ms.saturating_add(ms);
        stat.max_ms = stat.max_ms.max(ms);
        stat.last_up_ms = up_ms;
        if stat.count <= FULL_RECORDS_PER_NAME || took >= SLOW {
            let line = line("span", name, up_ms, Some(ms), note, fields);
            self.write(&line);
        }
        self.maybe_aggregate();
    }

    /// Records that something happened.
    pub fn event(
        &mut self,
        name: &'static str,
        note: &'static str,
        fields: &[(&'static str, u64)],
    ) {
        let up_ms = self.up_ms();
        let stat = self.stats.entry(name).or_default();
        stat.count += 1;
        stat.last_up_ms = up_ms;
        if stat.count <= FULL_RECORDS_PER_NAME {
            let line = line("event", name, up_ms, None, note, fields);
            self.write(&line);
        }
        self.maybe_aggregate();
    }

    /// Writes the counts and totals of every name that changed since the last time.
    pub fn flush(&mut self) {
        let changed: Vec<(&'static str, Stat)> = self
            .stats
            .iter()
            .filter(|(_, stat)| stat.count != stat.reported_count)
            .map(|(name, stat)| (*name, *stat))
            .collect();
        for (name, stat) in changed {
            let up_ms = self.up_ms();
            self.write(&json!({
                "s": self.session, "up": up_ms, "ev": "agg", "n": name,
                "count": stat.count, "total_ms": stat.total_ms, "max_ms": stat.max_ms,
                "last_up": stat.last_up_ms,
            }));
            if let Some(stat) = self.stats.get_mut(name) {
                stat.reported_count = stat.count;
            }
        }
        self.last_aggregate = Instant::now();
    }

    fn maybe_aggregate(&mut self) {
        if self.last_aggregate.elapsed() >= AGGREGATE_EVERY {
            self.flush();
        }
    }

    fn up_ms(&self) -> u64 {
        u64::try_from(self.start.elapsed().as_millis()).unwrap_or(u64::MAX)
    }

    fn write(&mut self, value: &Value) {
        // The cap keeps a runaway loop from pushing every earlier session out of the files.
        if self.lines >= SESSION_LINE_CAP {
            return;
        }
        self.lines += 1;
        let mut value = value.clone();
        if let Value::Object(map) = &mut value {
            map.entry("s").or_insert_with(|| json!(self.session));
            map.entry("t").or_insert_with(unix_ms);
        }
        let mut text = value.to_string();
        text.push('\n');
        let bytes = text.len() as u64;
        if self.size + bytes > MAX_FILE_BYTES {
            // Replaces the previous half: the log never holds more than two files.
            let _ = sandbox::rename_file(&self.base, &self.log, &self.previous);
            self.size = 0;
        }
        let appended = if sandbox::exists(&self.base, &self.log).unwrap_or(false) {
            sandbox::append_file(&self.base, &self.log, text.as_bytes())
        } else {
            let created = sandbox::write_file(&self.base, &self.log, text.as_bytes());
            // Timing records are for the owner, whatever the umask and the directory's mode.
            let _ = std::fs::set_permissions(
                &self.log,
                std::os::unix::fs::PermissionsExt::from_mode(0o600),
            );
            created
        };
        if appended.is_ok() {
            self.size += bytes;
        }
    }
}

fn unix_ms() -> Value {
    json!(
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |since| u64::try_from(since.as_millis()).unwrap_or(0))
    )
}

fn line(
    kind: &str,
    name: &str,
    up_ms: u64,
    ms: Option<u64>,
    note: &str,
    fields: &[(&'static str, u64)],
) -> Value {
    let mut value = json!({"up": up_ms, "ev": kind, "n": name});
    if let Value::Object(map) = &mut value {
        if let Some(ms) = ms {
            map.insert("ms".into(), json!(ms));
        }
        if !note.is_empty() {
            map.insert("note".into(), json!(note));
        }
        for (key, number) in fields {
            map.insert((*key).into(), json!(number));
        }
    }
    value
}

static GLOBAL: OnceLock<Mutex<Perf>> = OnceLock::new();

/// Starts recording for this process, under `base/.teamtypev`. Does nothing if that directory
/// does not exist or recording already started.
pub fn init(base: &Path) {
    if !base.join(".teamtypev").is_dir() {
        return;
    }
    let _ = GLOBAL.set(Mutex::new(Perf::open(base)));
}

fn with(action: impl FnOnce(&mut Perf)) {
    if let Some(perf) = GLOBAL.get()
        && let Ok(mut perf) = perf.lock()
    {
        action(&mut perf);
    }
}

/// Records one finished operation.
pub fn span(name: &'static str, took: Duration, fields: &[(&'static str, u64)]) {
    with(|perf| perf.span(name, took, "", fields));
}

/// Records one finished operation with a short fixed note (for example "retry").
pub fn span_note(
    name: &'static str,
    took: Duration,
    note: &'static str,
    fields: &[(&'static str, u64)],
) {
    with(|perf| perf.span(name, took, note, fields));
}

/// Records that something happened.
pub fn event(name: &'static str, fields: &[(&'static str, u64)]) {
    with(|perf| perf.event(name, "", fields));
}

/// Writes the pending counts and totals.
pub fn flush() {
    with(Perf::flush);
}

/// Times an operation until [`Timer::done`] is called or it is dropped.
#[must_use]
pub struct Timer {
    name: &'static str,
    start: Instant,
    done: bool,
}

/// Starts timing `name`.
pub fn timer(name: &'static str) -> Timer {
    Timer {
        name,
        start: Instant::now(),
        done: false,
    }
}

impl Timer {
    pub fn elapsed(&self) -> Duration {
        self.start.elapsed()
    }

    /// Records the duration with `fields`.
    pub fn done(mut self, fields: &[(&'static str, u64)]) {
        self.done = true;
        span(self.name, self.start.elapsed(), fields);
    }
}

impl Drop for Timer {
    fn drop(&mut self) {
        if !self.done {
            span(self.name, self.start.elapsed(), &[]);
        }
    }
}

/// Summary of the latest recorded session, for pasting into a message.
pub fn report(base: &Path) -> String {
    let mut lines = vec![];
    for name in ["perf.log.1", "perf.log"] {
        if let Ok(bytes) = sandbox::read_file(base, &base.join(".teamtypev").join(name)) {
            lines.extend(
                String::from_utf8_lossy(&bytes)
                    .lines()
                    .filter_map(|line| serde_json::from_str::<Value>(line).ok()),
            );
        }
    }
    summarize(&lines)
}

/// Seconds with milliseconds, from a millisecond count.
fn seconds(ms: u64) -> String {
    format!("{}.{:03}", ms / 1000, ms % 1000)
}

fn summarize(lines: &[Value]) -> String {
    use std::fmt::Write;
    let Some(session) = lines
        .iter()
        .rev()
        .find(|line| line["ev"] == "session")
        .map(|line| line["s"].clone())
    else {
        return "No timing records yet. Run teamtypev share or join first.\n".into();
    };
    let mine: Vec<&Value> = lines.iter().filter(|line| line["s"] == session).collect();
    let mut out = String::new();
    if let Some(header) = mine.iter().find(|line| line["ev"] == "session") {
        let _ = writeln!(
            out,
            "teamtypev {} on {} {} ({} cpus), session {}",
            header["version"].as_str().unwrap_or("?"),
            header["os"].as_str().unwrap_or("?"),
            header["arch"].as_str().unwrap_or("?"),
            header["cpus"],
            session.as_str().unwrap_or("?"),
        );
    }
    out += "\nTimeline (seconds since start; durations in ms):\n";
    for line in mine
        .iter()
        .filter(|line| line["ev"] != "agg" && line["ev"] != "session")
    {
        let up = line["up"].as_u64().unwrap_or(0);
        let ms = line["ms"].as_u64();
        let start = ms.map_or(up, |ms| up.saturating_sub(ms));
        let _ = write!(
            out,
            "  +{:>7}s  {:<28}",
            seconds(start),
            line["n"].as_str().unwrap_or("?")
        );
        if let Some(ms) = ms {
            let _ = write!(out, " {ms:>6} ms");
        }
        if let Some(note) = line["note"].as_str() {
            let _ = write!(out, "  {note}");
        }
        if let Value::Object(map) = line {
            for (key, value) in map {
                if !["up", "ev", "n", "ms", "note", "s", "t"].contains(&key.as_str()) {
                    let _ = write!(out, "  {key}={value}");
                }
            }
        }
        out += "\n";
    }
    // The last aggregate line of each name holds its totals since the start.
    let mut totals: BTreeMap<String, &Value> = BTreeMap::new();
    for line in mine.iter().filter(|line| line["ev"] == "agg") {
        totals.insert(line["n"].as_str().unwrap_or("?").to_owned(), line);
    }
    if !totals.is_empty() {
        out += "\nTotals since start (name, count, total ms, max ms, last at s):\n";
        let mut rows: Vec<_> = totals.into_iter().collect();
        rows.sort_by_key(|(_, line)| std::cmp::Reverse(line["total_ms"].as_u64().unwrap_or(0)));
        for (name, line) in rows {
            let _ = writeln!(
                out,
                "  {name:<28} {:>7} {:>9} {:>7}  {:>8}",
                line["count"],
                line["total_ms"],
                line["max_ms"],
                seconds(line["last_up"].as_u64().unwrap_or(0)),
            );
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dir() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir(dir.path().join(".teamtypev")).unwrap();
        dir
    }

    fn size_of_logs(dir: &Path) -> u64 {
        ["perf.log", "perf.log.1"]
            .iter()
            .map(|name| std::fs::metadata(dir.join(".teamtypev").join(name)).map_or(0, |m| m.len()))
            .sum()
    }

    #[test]
    fn records_hold_numbers_and_names_only() {
        let dir = dir();
        let mut perf = Perf::open(dir.path());
        perf.span(
            "join.test",
            Duration::from_millis(12),
            "retry",
            &[("files", 3)],
        );
        let text = std::fs::read_to_string(dir.path().join(".teamtypev/perf.log")).unwrap();
        let lines: Vec<Value> = text
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        assert_eq!(lines[0]["ev"], "session");
        assert_eq!(lines[1]["n"], "join.test");
        assert_eq!(lines[1]["ms"], 12);
        assert_eq!(lines[1]["files"], 3);
        assert_eq!(lines[1]["note"], "retry");
        let mode = std::fs::metadata(dir.path().join(".teamtypev/perf.log"))
            .unwrap()
            .permissions();
        assert_eq!(std::os::unix::fs::PermissionsExt::mode(&mode) & 0o077, 0);
    }

    #[test]
    fn frequent_names_are_counted_but_only_the_first_and_slow_ones_are_written() {
        let dir = dir();
        let mut perf = Perf::open(dir.path());
        for _ in 0..10_000 {
            perf.span("frequent", Duration::from_millis(1), "", &[]);
        }
        perf.span("frequent", Duration::from_millis(900), "", &[]);
        perf.flush();
        let text = std::fs::read_to_string(dir.path().join(".teamtypev/perf.log")).unwrap();
        let spans = text.lines().filter(|l| l.contains("\"span\"")).count();
        assert_eq!(spans as u64, FULL_RECORDS_PER_NAME + 1);
        let agg: Value =
            serde_json::from_str(text.lines().rev().find(|l| l.contains("\"agg\"")).unwrap())
                .unwrap();
        assert_eq!(agg["count"], 10_001);
        assert_eq!(agg["max_ms"], 900);
        assert_eq!(agg["total_ms"], 10_000 + 900);
    }

    #[test]
    fn the_log_never_exceeds_two_files_of_the_size_limit() {
        let dir = dir();
        // Many sessions, each filling its line cap with distinct slow records.
        for _ in 0..8 {
            let mut perf = Perf::open(dir.path());
            for _ in 0..(SESSION_LINE_CAP * 2) {
                perf.span(
                    "slow",
                    Duration::from_secs(1),
                    "",
                    &[("bytes", 123_456_789)],
                );
            }
            assert!(perf.lines <= SESSION_LINE_CAP);
        }
        assert!(
            size_of_logs(dir.path()) <= 2 * MAX_FILE_BYTES + 1024,
            "{}",
            size_of_logs(dir.path())
        );
        assert!(dir.path().join(".teamtypev/perf.log.1").exists());
    }

    #[test]
    fn nothing_is_written_without_a_teamtypev_directory_or_before_init() {
        let dir = tempfile::tempdir().unwrap();
        init(dir.path());
        span("ignored", Duration::from_millis(1), &[]);
        assert!(!dir.path().join(".teamtypev").exists());
    }

    #[test]
    fn the_report_shows_the_timeline_and_totals_of_the_latest_session() {
        let dir = dir();
        let mut old = Perf::open(dir.path());
        old.span("old.session", Duration::from_millis(5), "", &[]);
        let mut perf = Perf::open(dir.path());
        std::thread::sleep(Duration::from_millis(2));
        perf.span("join.resolve_peer", Duration::from_millis(1), "", &[]);
        perf.span(
            "peer.connect",
            Duration::from_millis(1500),
            "direct",
            &[("attempt", 1)],
        );
        for _ in 0..3 {
            perf.span("doc.write", Duration::from_millis(40), "", &[]);
        }
        perf.flush();
        let report = report(dir.path());
        assert!(report.contains("join.resolve_peer"), "{report}");
        assert!(report.contains("peer.connect"), "{report}");
        assert!(report.contains("1500 ms"), "{report}");
        assert!(report.contains("attempt=1"), "{report}");
        assert!(!report.contains("old.session"), "{report}");
        assert!(report.contains("doc.write"), "{report}");
        assert!(report.contains("Totals since start"), "{report}");
    }
}
