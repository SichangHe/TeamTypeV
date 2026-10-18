// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

//! One guarded edit sent to the running daemon as a short-lived editor.
//!
//! Going through the daemon instead of the file on disk matters because the daemon ignores disk
//! changes to a file that an editor has open.

use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result, bail};
use futures::{SinkExt, StreamExt};
use serde_json::Value;
use teamtype::editor_protocol::{EditorProtocolMessageFromEditor, IncomingMessage};
use teamtype::jsonrpc_forwarder::{JSONRPCForwarder, UnixJSONRPCForwarder};
use teamtype::path::AbsolutePath;
use teamtype::types::{EditorTextDelta, EditorTextOp, TextDelta};

const OPEN_ID: usize = 1;
const BARRIER_ID: usize = 2;
const EDIT_ID: usize = 3;
const TIMEOUT: Duration = Duration::from_secs(30);

/// The single replacement that turns `expected` into `replacement`, or `None` if they are equal.
/// The daemon accepts at most one operation per edit, so the common prefix and suffix are kept and
/// the middle is replaced; concurrent edits outside the middle then merge instead of being lost.
fn single_op(expected: &str, replacement: &str) -> Result<Option<EditorTextOp>> {
    let old: Vec<char> = expected.chars().collect();
    let new: Vec<char> = replacement.chars().collect();
    let n_prefix = old.iter().zip(&new).take_while(|(a, b)| a == b).count();
    let n_suffix = old[n_prefix..]
        .iter()
        .rev()
        .zip(new[n_prefix..].iter().rev())
        .take_while(|(a, b)| a == b)
        .count();
    let n_deleted = old.len() - n_prefix - n_suffix;
    let inserted: String = new[n_prefix..new.len() - n_suffix].iter().collect();
    let mut delta = TextDelta::default();
    delta.retain(n_prefix);
    if n_deleted > 0 {
        delta.delete(n_deleted);
    } else if inserted.is_empty() {
        return Ok(None);
    } else {
        delta.insert(&inserted);
    }
    let mut op = EditorTextDelta::try_from_delta(delta, expected)?
        .0
        .pop()
        .context("Delta produced no operation")?;
    op.replacement = inserted;
    Ok(Some(op))
}

/// `current` with its only occurrence of `old` replaced by `new`.
fn replace_once(current: &str, old: &str, new: &str) -> Result<String> {
    if old.is_empty() {
        bail!("Agent edit rejected: the text to replace is empty");
    }
    match current.matches(old).count() {
        1 => Ok(current.replacen(old, new, 1)),
        0 => bail!(
            "Agent edit rejected: the text to replace is not in the file; it may have changed, so read it again"
        ),
        n => bail!(
            "Agent edit rejected: the text to replace occurs {n} times; include more context to make it unique"
        ),
    }
}

// 🧑 "support an agent command line tool whose edits cannot be silently overwritten by editor edits"
// 🧑 "make sure this actually works and that agents cannot overwrite editor changes"
/// Replaces the only occurrence of `old` in `file` with `new`, or fails without changing anything.
///
/// The edit is computed from the file's current content on disk, which the daemon writes, so a
/// stale snapshot held by the caller cannot revert other people's changes. The daemon then opens
/// the file with that content and answers with an edit only if its own content differs; a cursor
/// request without ranges follows as a barrier: its response arrives after any such edit. Edits
/// by others that arrive after the barrier are merged by the daemon like concurrent edits between
/// editors.
pub async fn run(directory: &Path, file: &Path, old: &str, new: &str) -> Result<()> {
    let path = directory.join(file);
    // The daemon would create a missing file with `expected` as its content.
    if !path.is_file() {
        bail!("Agent edit rejected: {} is not a file", path.display());
    }
    let expected = std::fs::read_to_string(&path)
        .with_context(|| format!("Could not read {}", path.display()))?;
    let replacement = replace_once(&expected, old, new)?;
    let Some(op) = single_op(&expected, &replacement)? else {
        return Ok(());
    };
    let uri = AbsolutePath::try_from(path)?.to_file_uri().to_string();
    tokio::time::timeout(TIMEOUT, exchange(directory, uri, expected, op))
        .await
        .context("Daemon did not answer the agent edit in time")?
}

async fn exchange(directory: &Path, uri: String, expected: String, op: EditorTextOp) -> Result<()> {
    let (mut from_daemon, mut to_daemon) = UnixJSONRPCForwarder {}
        .connect_stream(directory)
        .await
        .context("Agent edit needs a running daemon (`teamtype share` or `teamtype join`)")?;
    let requests = [
        (
            OPEN_ID,
            EditorProtocolMessageFromEditor::Open {
                uri: uri.clone(),
                content: expected,
                saves_file: false,
            },
        ),
        (
            BARRIER_ID,
            EditorProtocolMessageFromEditor::Cursor {
                uri: uri.clone(),
                ranges: vec![],
            },
        ),
    ];
    for (id, payload) in requests {
        let request = IncomingMessage::Request {
            id: id.into(),
            payload,
        };
        to_daemon.send(serde_json::to_string(&request)?).await?;
    }
    let mut edit = Some(IncomingMessage::Request {
        id: EDIT_ID.into(),
        payload: EditorProtocolMessageFromEditor::Edit {
            uri: uri.clone(),
            revision: 0,
            delta: EditorTextDelta(vec![op]),
        },
    });
    while let Some(line) = from_daemon.next().await {
        let message: Value = serde_json::from_str(&line?)?;
        if let Some(error) = message.get("error") {
            bail!("Agent edit rejected: {error}");
        }
        if message["method"] == "edit" && message["params"]["uri"] == uri.as_str() && edit.is_some()
        {
            bail!(
                "Agent edit rejected: the file changed while editing, or an editor has unsaved changes; try again"
            );
        }
        if message["id"] == BARRIER_ID
            && let Some(edit) = edit.take()
        {
            to_daemon.send(serde_json::to_string(&edit)?).await?;
        }
        if message["id"] == EDIT_ID {
            let close = IncomingMessage::Request {
                id: (EDIT_ID + 1).into(),
                payload: EditorProtocolMessageFromEditor::Close { uri },
            };
            to_daemon.send(serde_json::to_string(&close)?).await?;
            // The daemon writes the file to disk when it handles the close.
            while let Some(line) = from_daemon.next().await {
                let message: Value = serde_json::from_str(&line?)?;
                if message["id"] == EDIT_ID + 1 {
                    return Ok(());
                }
            }
            break;
        }
    }
    bail!("Daemon closed the connection before confirming the agent edit")
}

// 🧑 "Does Teamtype give you a good way to see diffs from your last read/write? How should it be
// best done if not already?"
/// Where `agent`'s snapshot of `file` is kept: the content it last read or wrote.
fn snapshot_path(directory: &Path, agent: &str, file: &Path) -> PathBuf {
    directory
        .join(".teamtype/agent-snapshots")
        .join(agent)
        .join(file)
}

/// Remembers `file`'s current content as `agent`'s snapshot.
pub fn save_snapshot(directory: &Path, agent: &str, file: &Path) -> Result<()> {
    let content = std::fs::read(directory.join(file))
        .with_context(|| format!("Could not read {}", file.display()))?;
    let snapshot = snapshot_path(directory, agent, file);
    if let Some(parent) = snapshot.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(&snapshot, content)?;
    Ok(())
}

/// Prints `file` and remembers it as `agent`'s snapshot.
pub fn read(directory: &Path, agent: &str, file: &Path) -> Result<()> {
    let content = std::fs::read_to_string(directory.join(file))
        .with_context(|| format!("Could not read {}", file.display()))?;
    print!("{content}");
    save_snapshot(directory, agent, file)
}

/// Prints unified diffs from `agent`'s snapshots to the current content, of `file` or of every
/// file the agent has a snapshot of.
pub fn diff(directory: &Path, agent: &str, file: Option<&Path>) -> Result<()> {
    let root = directory.join(".teamtype/agent-snapshots").join(agent);
    let files: Vec<PathBuf> = match file {
        Some(file) => vec![file.to_path_buf()],
        None => walk(&root)
            .into_iter()
            .filter_map(|path| path.strip_prefix(&root).ok().map(Path::to_path_buf))
            .collect(),
    };
    for file in files {
        let Ok(old) = std::fs::read_to_string(snapshot_path(directory, agent, &file)) else {
            println!(
                "No snapshot of {} for {agent}; use agent-read first.",
                file.display()
            );
            continue;
        };
        let new = std::fs::read_to_string(directory.join(&file)).unwrap_or_default();
        if old != new {
            let name = file.display().to_string();
            print!(
                "{}",
                similar::TextDiff::from_lines(&old, &new)
                    .unified_diff()
                    .header(
                        &format!("{name} (last read or written)"),
                        &format!("{name} (now)")
                    )
            );
        }
    }
    Ok(())
}

fn walk(dir: &Path) -> Vec<PathBuf> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return vec![];
    };
    entries
        .flatten()
        .flat_map(|entry| {
            let path = entry.path();
            if path.is_dir() {
                walk(&path)
            } else {
                vec![path]
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn op(expected: &str, replacement: &str) -> (usize, usize, usize, usize, String) {
        let op = single_op(expected, replacement).unwrap().unwrap();
        let (start, end) = (op.range.start, op.range.end);
        (
            start.line,
            start.character,
            end.line,
            end.character,
            op.replacement,
        )
    }

    #[test]
    fn single_op_replaces_only_the_differing_middle() {
        assert!(single_op("same", "same").unwrap().is_none());
        assert_eq!(op("a\nb\n", "a\nb\nc\n"), (2, 0, 2, 0, "c\n".into()));
        assert_eq!(op("a\nxyz\n", "a\nxQz\n"), (1, 1, 1, 2, "Q".into()));
        assert_eq!(op("a\nb\nc\n", "a\nc\n"), (1, 0, 2, 0, String::new()));
        assert_eq!(op("aa", "a"), (0, 1, 0, 2, String::new()));
    }

    #[test]
    fn snapshots_follow_reads() {
        let dir = tempfile::tempdir().unwrap();
        let file = Path::new("sub/f.txt");
        std::fs::create_dir_all(dir.path().join("sub")).unwrap();
        std::fs::write(dir.path().join(file), "one\n").unwrap();
        read(dir.path(), "ann", file).unwrap();
        std::fs::write(dir.path().join(file), "two\n").unwrap();
        let snapshot = std::fs::read_to_string(snapshot_path(dir.path(), "ann", file)).unwrap();
        assert_eq!(snapshot, "one\n");
        diff(dir.path(), "ann", None).unwrap();
        save_snapshot(dir.path(), "ann", file).unwrap();
        let snapshot = std::fs::read_to_string(snapshot_path(dir.path(), "ann", file)).unwrap();
        assert_eq!(snapshot, "two\n");
    }

    #[test]
    fn replace_once_needs_exactly_one_occurrence() {
        assert_eq!(replace_once("a b c", "b", "B").unwrap(), "a B c");
        assert!(replace_once("a b c", "x", "B").is_err());
        assert!(replace_once("a b b", "b", "B").is_err());
        assert!(replace_once("a b c", "", "B").is_err());
    }
}
