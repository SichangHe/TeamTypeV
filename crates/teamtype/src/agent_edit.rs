// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

//! One guarded edit sent to the running daemon as a short-lived editor.
//!
//! Going through the daemon instead of the file on disk matters because the daemon ignores disk
//! changes to a file that an editor has open.

use std::io::Write;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
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
    match current
        .char_indices()
        .filter(|(at, _)| current[*at..].starts_with(old))
        .count()
    {
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
/// Replaces the only occurrence of `old` in `file` with `new`, returning the agent's post-edit
/// view for its snapshot, or fails without changing anything.
///
/// The edit is computed from the file's current content on disk, which the daemon writes, so a
/// stale snapshot held by the caller cannot revert other people's changes. The daemon then opens
/// the file with that content and answers with an edit only if its own content differs; a cursor
/// request without ranges follows as a barrier: its response arrives after any such edit. Edits
/// by others that arrive after the barrier are merged by the daemon like concurrent edits between
/// editors.
pub async fn run(directory: &Path, file: &Path, old: &str, new: &str) -> Result<String> {
    let path = directory.join(file);
    // The daemon would create a missing file with `expected` as its content.
    if !path.is_file() {
        bail!("Agent edit rejected: {} is not a file", path.display());
    }
    let expected = String::from_utf8(teamtype::sandbox::read_file(directory, &path)?)
        .with_context(|| format!("Could not read {}", path.display()))?;
    let replacement = replace_once(&expected, old, new)?;
    let Some(op) = single_op(&expected, &replacement)? else {
        return Ok(replacement);
    };
    let uri = AbsolutePath::try_from(path)?.to_file_uri().to_string();
    tokio::time::timeout(TIMEOUT, exchange(directory, uri, expected, op))
        .await
        .context("Daemon did not answer the agent edit in time")??;
    Ok(replacement)
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
fn snapshot_root(directory: &Path, agent: &str) -> Result<PathBuf> {
    if !matches!(
        Path::new(agent).components().next(),
        Some(Component::Normal(_))
    ) || Path::new(agent).file_name() != Some(std::ffi::OsStr::new(agent))
    {
        bail!("Agent name must be one path component");
    }
    let legacy = directory.join(".teamtype/agent-snapshots");
    if teamtype::sandbox::exists(directory, &legacy)? {
        if std::fs::symlink_metadata(&legacy)?.file_type().is_symlink() {
            bail!("Legacy snapshot root must not be a symlink");
        }
        std::fs::set_permissions(&legacy, std::fs::Permissions::from_mode(0o700))?;
    }
    let root = directory.join(".teamtype/agent-snapshots-v2");
    let agent_root = root.join(agent);
    // Only Teamtype directories hold snapshots; never create `.teamtype` as a side effect.
    if !directory.join(".teamtype").is_dir() {
        bail!(
            "{} is not a Teamtype directory (no .teamtype); run agent commands inside a shared directory",
            directory.display()
        );
    }
    for path in [&root, &agent_root] {
        match std::fs::DirBuilder::new().mode(0o700).create(path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.into()),
        }
        let metadata = std::fs::symlink_metadata(path)?;
        if !metadata.is_dir() {
            bail!("Snapshot directories must not be symlinks or regular files");
        }
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700))?;
    }
    Ok(agent_root)
}

fn snapshot_path(directory: &Path, agent: &str, file: &Path) -> Result<PathBuf> {
    if file.as_os_str().is_empty()
        || !file
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
    {
        bail!("Snapshot file must be a relative path without parent components");
    }
    let name = file.to_str().context("Snapshot path is not UTF-8")?;
    Ok(snapshot_root(directory, agent)?.join(blake3::hash(name.as_bytes()).to_hex().as_str()))
}

/// Checks the snapshot destination before attempting an edit.
pub fn prepare_snapshot(directory: &Path, agent: &str, file: &Path) -> Result<()> {
    let snapshot = snapshot_path(directory, agent, file)?;
    if std::fs::symlink_metadata(&snapshot).is_ok_and(|metadata| !metadata.is_file()) {
        bail!("Snapshot destination must be a regular file in its agent directory");
    }
    match load_snapshot(&snapshot) {
        Ok((saved_file, _)) if saved_file != file => bail!("Snapshot path collision"),
        Ok(_) => Ok(()),
        Err(error)
            if error
                .downcast_ref::<std::io::Error>()
                .is_some_and(|error| error.kind() == std::io::ErrorKind::NotFound) =>
        {
            Ok(())
        }
        Err(error) => Err(error),
    }
}

/// Each bounded filename has a record containing the original path and observed text.
fn load_snapshot(snapshot: &Path) -> Result<(PathBuf, String)> {
    Ok(serde_json::from_slice(&std::fs::read(snapshot)?)?)
}

/// Remembers the exact content the agent read or wrote, without rereading disk.
pub fn save_snapshot(directory: &Path, agent: &str, file: &Path, content: &[u8]) -> Result<()> {
    prepare_snapshot(directory, agent, file)?;
    let snapshot = snapshot_path(directory, agent, file)?;
    let parent = snapshot.parent().context("Snapshot has no parent")?;
    let mut output = tempfile::NamedTempFile::new_in(parent)?;
    serde_json::to_writer(&mut output, &(file, std::str::from_utf8(content)?))?;
    output.persist(snapshot)?;
    Ok(())
}

/// Prints `file` and remembers it as `agent`'s snapshot.
pub fn read(directory: &Path, agent: &str, file: &Path) -> Result<()> {
    prepare_snapshot(directory, agent, file)?;
    let content = String::from_utf8(teamtype::sandbox::read_file(
        directory,
        &directory.join(file),
    )?)
    .with_context(|| format!("Could not read {}", file.display()))?;
    let mut stdout = std::io::stdout().lock();
    stdout.write_all(content.as_bytes())?;
    stdout.flush()?;
    save_snapshot(directory, agent, file, content.as_bytes())
}

/// Prints unified diffs from `agent`'s snapshots to the current content, of `file` or of every
/// file the agent has a snapshot of.
pub fn diff(directory: &Path, agent: &str, file: Option<&Path>) -> Result<()> {
    let root = snapshot_root(directory, agent)?;
    if let Some(file) = file {
        snapshot_path(directory, agent, file)?;
    }
    let files: Vec<PathBuf> = file.map_or_else(
        || {
            std::fs::read_dir(&root)
                .into_iter()
                .flatten()
                .filter_map(|entry| {
                    load_snapshot(&entry.ok()?.path())
                        .ok()
                        .map(|(file, _)| file)
                })
                .collect()
        },
        |file| vec![file.to_path_buf()],
    );
    for file in files {
        let Ok((saved_file, old)) = load_snapshot(&snapshot_path(directory, agent, &file)?) else {
            println!(
                "No snapshot of {} for {agent}; use agent-read first.",
                file.display()
            );
            continue;
        };
        anyhow::ensure!(saved_file == file, "Snapshot path collision");
        let new = teamtype::sandbox::read_file(directory, &directory.join(&file))
            .ok()
            .and_then(|bytes| String::from_utf8(bytes).ok())
            .unwrap_or_default();
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
    fn snapshots_need_a_teamtype_directory_and_never_create_one() {
        let dir = tempfile::tempdir().unwrap();
        assert!(snapshot_path(dir.path(), "ann", Path::new("f.txt")).is_err());
        assert!(!dir.path().join(".teamtype").exists());
    }

    #[test]
    fn snapshots_follow_reads() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir(dir.path().join(".teamtype")).unwrap();
        let file = Path::new("sub/f.txt");
        std::fs::create_dir_all(dir.path().join("sub")).unwrap();
        std::fs::write(dir.path().join(file), "one\n").unwrap();
        read(dir.path(), "ann", file).unwrap();
        std::fs::write(dir.path().join(file), "two\n").unwrap();
        let snapshot =
            load_snapshot(&snapshot_path(dir.path(), "ann", file).expect("snapshot path"))
                .expect("snapshot")
                .1;
        assert_eq!(snapshot, "one\n");
        diff(dir.path(), "ann", None).expect("diff");
        save_snapshot(dir.path(), "ann", file, b"two\n").expect("save snapshot");
        let snapshot =
            load_snapshot(&snapshot_path(dir.path(), "ann", file).expect("snapshot path"))
                .expect("snapshot")
                .1;
        assert_eq!(snapshot, "two\n");
    }

    #[test]
    fn replace_once_needs_exactly_one_occurrence() {
        assert_eq!(replace_once("a b c", "b", "B").unwrap(), "a B c");
        assert!(replace_once("a b c", "x", "B").is_err());
        assert!(replace_once("a b b", "b", "B").is_err());
        assert!(replace_once("a b c", "", "B").is_err());
        assert!(replace_once("aaa", "aa", "X").is_err());
        assert!(replace_once("ééé", "éé", "X").is_err());
    }

    #[test]
    fn snapshot_names_cannot_escape_or_collide_after_file_directory_changes() {
        let dir = tempfile::tempdir().expect("project");
        std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata");
        assert!(snapshot_path(dir.path(), "..", Path::new("config")).is_err());
        assert!(snapshot_path(dir.path(), "ann", Path::new("/tmp/source")).is_err());
        assert!(snapshot_path(dir.path(), "ann", Path::new("../config")).is_err());
        save_snapshot(dir.path(), "ann", Path::new("a"), b"old parent").expect("parent snapshot");
        save_snapshot(dir.path(), "ann", Path::new("a/b"), b"new child").expect("child snapshot");
        save_snapshot(dir.path(), "ann", Path::new("a"), b"parent again").expect("parent update");
        let parent = snapshot_path(dir.path(), "ann", Path::new("a")).expect("parent path");
        let child = snapshot_path(dir.path(), "ann", Path::new("a/b")).expect("child path");
        assert_eq!(
            load_snapshot(&parent).expect("parent record").1,
            "parent again"
        );
        assert_eq!(load_snapshot(&child).expect("child record").1, "new child");
    }

    #[test]
    fn single_op_preserves_unicode_prefix_and_multiline_suffix() {
        assert_eq!(
            op("é🙂中\nkeep\n", "é🙂文\nkeep\n"),
            (0, 2, 0, 3, "文".into())
        );
        assert_eq!(
            op("é\n🙂\nend", "é\n中\n文\nend"),
            (1, 0, 1, 1, "中\n文".into())
        );
        assert_eq!(op("", "🙂\n"), (0, 0, 0, 0, "🙂\n".into()));
        assert_eq!(op("🙂\n", ""), (0, 0, 1, 0, String::new()));
    }
}
