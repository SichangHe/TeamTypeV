// SPDX-License-Identifier: AGPL-3.0-or-later

#[test]
fn git_completion_preserves_files_created_in_shared_history() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let path = RelativePath::new("new-peer-file");
    assert!(actor.start_git(&[])?);
    actor.crdt_doc.update_text("created during Git", &path);
    actor.write_file(&path);
    assert!(!dir.path().join("new-peer-file").exists());
    actor.finish_git()?;
    actor.assert_file_content(&path, "created during Git");
    assert_eq!(
        std::fs::read_to_string(dir.path().join("new-peer-file"))?,
        "created during Git"
    );
    Ok(())
}

#[tokio::test]
async fn opening_missing_file_during_git_requires_retry_without_creating_it() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let (_uri, _reader) = open_test_editor(&mut actor, &RelativePath::new("file1")).await;
    assert!(actor.start_git(&[])?);
    let path = RelativePath::new("new-file");
    let request = EditorProtocolMessageFromEditor::Open {
        uri: actor
            .absolute_path_for_file_path(&path)
            .to_file_uri()
            .to_string(),
        content: "new content".into(),
        saves_file: false,
        daemon_writes: true,
    };
    let error = actor
        .react_to_message_from_editor(1, &request)
        .await
        .expect_err("Git owns disk writes");
    assert!(error.message.contains("retry opening"));
    assert!(!dir.path().join("new-file").exists());
    actor.finish_git()?;
    actor
        .react_to_message_from_editor(1, &request)
        .await
        .expect("retry open after Git");
    assert_eq!(
        std::fs::read_to_string(dir.path().join("new-file"))?,
        "new content"
    );
    Ok(())
}

async fn open_test_editor(
    actor: &mut DocumentActor,
    path: &RelativePath,
) -> (String, tokio::net::UnixStream) {
    let uri = actor
        .absolute_path_for_file_path(path)
        .to_file_uri()
        .to_string();
    let (stream, reader) = tokio::net::UnixStream::pair().expect("editor socket");
    let (_, writer) = tokio::io::split(stream);
    actor.editor_connections.insert(
        1,
        (
            EditorConnection::new("test".into(), actor.app_config.clone()),
            tokio_util::codec::FramedWrite::new(writer, editor::OutgoingProtocolCodec),
        ),
    );
    actor
        .react_to_message_from_editor(
            1,
            &EditorProtocolMessageFromEditor::Open {
                uri: uri.clone(),
                content: "content1".into(),
                saves_file: false,
                daemon_writes: true,
            },
        )
        .await
        .expect("open");
    (uri, reader)
}

#[tokio::test]
async fn binary_round_trip_requires_editor_reopen() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let path = RelativePath::new("file1");
    let (uri, _reader) = open_test_editor(&mut actor, &path).await;
    std::fs::write(dir.path().join("file1"), [0xff])?;
    actor.file_created_or_changed(&path);
    std::fs::write(dir.path().join("file1"), b"different text")?;
    actor.file_created_or_changed(&path);
    let edit = TextDelta::from(dissimilar::diff("content1", "Qontent1"));
    assert!(
        actor
            .react_to_message_from_editor(
                1,
                &EditorProtocolMessageFromEditor::Edit {
                    uri: uri.clone(),
                    revision: 0,
                    delta: crate::types::EditorTextDelta::try_from_delta(edit, "content1")?,
                }
            )
            .await
            .is_err(),
        "stale buffer must not edit replacement text"
    );
    assert!(
        actor
            .react_to_message_from_editor(
                1,
                &EditorProtocolMessageFromEditor::Save { uri: uri.clone() }
            )
            .await
            .is_err(),
        "stale buffer must not report a successful save"
    );
    actor.assert_file_content(&path, "different text");
    assert_eq!(std::fs::read(dir.path().join("file1"))?, b"different text");
    actor
        .react_to_message_from_editor(
            1,
            &EditorProtocolMessageFromEditor::Open {
                uri: uri.clone(),
                content: "different text".into(),
                saves_file: false,
                daemon_writes: true,
            },
        )
        .await
        .expect("reopen replacement");
    actor
        .react_to_message_from_editor(1, &EditorProtocolMessageFromEditor::Save { uri })
        .await
        .expect("save after reopen");
    Ok(())
}

#[tokio::test]
async fn failed_save_returns_error_and_can_be_retried() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let path = RelativePath::new("file1");
    let (uri, _reader) = open_test_editor(&mut actor, &path).await;
    actor.persist = true;
    let _ = actor.persist();
    actor.crdt_doc.update_text("unsaved typing", &path);
    std::fs::remove_dir_all(dir.path().join(".teamtypev"))?;
    std::fs::write(dir.path().join(".teamtypev"), b"occupied")?;
    let save = EditorProtocolMessageFromEditor::Save { uri };
    assert!(actor.react_to_message_from_editor(1, &save).await.is_err());
    assert!(actor.flush_git_files().is_err());
    actor.assert_file_content(&path, "unsaved typing");
    assert_eq!(std::fs::read(dir.path().join("file1"))?, b"content1");
    std::fs::remove_file(dir.path().join(".teamtypev"))?;
    actor
        .react_to_message_from_editor(1, &save)
        .await
        .expect("retry save");
    assert_eq!(std::fs::read(dir.path().join("file1"))?, b"unsaved typing");
    let recovered = Document::load(&std::fs::read(dir.path().join(".teamtypev/doc"))?);
    assert_eq!(
        recovered.current_file_content(&path),
        actor.current_file_content(&path)
    );
    Ok(())
}

#[test]
fn displaced_binary_bytes_are_reconciled() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let path = RelativePath::new("file1");
    actor
        .crdt_doc
        .set_file(document::Content::Bytes(vec![0xff, 1]), &path);
    std::fs::write(dir.path().join("file1"), [0xff, 2])?;
    let _ = actor.ensure_file_has_bytes(&path, &[0xff, 1]);
    assert_eq!(
        actor.current_file_content(&path),
        Some(&document::Content::Bytes(vec![0xff, 2]))
    );
    actor.write_file(&path);
    assert_eq!(std::fs::read(dir.path().join("file1"))?, [0xff, 2]);
    Ok(())
}

/// Starts a daemon over `dir` the way a restart after a crash does.
fn restarted_actor(dir: &TempDir) -> DocumentActor {
    let (_doc_message_tx, doc_message_rx) = mpsc::channel(1);
    let (doc_changed_ping_tx, _doc_changed_ping_rx) = broadcast::channel::<()>(1);
    let (ephemeral_message_tx, _ephemeral_message_rx) = broadcast::channel::<EphemeralMessage>(100);
    DocumentActor::new(
        doc_message_rx,
        doc_changed_ping_tx,
        ephemeral_message_tx,
        AppConfig {
            base_dir: dir.path().to_path_buf(),
            ..Default::default()
        },
        false,
        true,
        true,
    )
}

#[test]
fn crash_after_writing_a_peers_edit_does_not_duplicate_it_on_restart() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let path = RelativePath::new("shared");
    std::fs::write(dir.path().join("shared"), "line1\n")?;
    let mut actor = DocumentActor::setup_for_testing(&dir);
    actor.persist = true;
    actor.read_current_content_from_dir(true);
    actor.persist()?;
    // A peer's edit arrives and is applied, as in `ReceiveSyncMessage`.
    actor.crdt_doc.update_text("line1\npeer\n", &path);
    actor.mark_pending([path.clone()]);
    // The write reaches the disk (after saving the document), then the daemon is killed before
    // it clears the pending record.
    actor.ensure_file_has_bytes(&path, b"line1\npeer\n")?;
    drop(actor);
    assert!(dir.path().join(".teamtypev/pending-writes").exists());
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&path, "line1\npeer\n");
    assert_eq!(
        std::fs::read_to_string(dir.path().join("shared"))?,
        "line1\npeer\n"
    );
    Ok(())
}

/// A daemon over a persisted, shared file "shared" holding "line1\n", with a peer's edit applied
/// to the document and recorded as pending (the state right after `mark_pending`).
fn actor_with_pending_peer_edit(dir: &TempDir) -> Result<DocumentActor> {
    std::fs::write(dir.path().join("shared"), "line1\n")?;
    let mut actor = DocumentActor::setup_for_testing(dir);
    actor.persist = true;
    actor.read_current_content_from_dir(true);
    actor.persist()?;
    let path = RelativePath::new("shared");
    actor.crdt_doc.update_text("line1\npeer\n", &path);
    actor.mark_pending([path]);
    Ok(actor)
}

#[test]
fn crash_after_saving_the_document_before_writing_finishes_the_write() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    actor.persist()?;
    drop(actor);
    assert_eq!(std::fs::read(dir.path().join("shared"))?, b"line1\n");
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&RelativePath::new("shared"), "line1\npeer\n");
    assert_eq!(
        std::fs::read(dir.path().join("shared"))?,
        b"line1\npeer\n",
        "the interrupted write is finished, not read as an outside edit that reverts the peer"
    );
    Ok(())
}

#[test]
fn crash_before_saving_the_document_keeps_the_old_state() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    drop(actor_with_pending_peer_edit(&dir)?);
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&RelativePath::new("shared"), "line1\n");
    assert_eq!(std::fs::read(dir.path().join("shared"))?, b"line1\n");
    Ok(())
}

#[test]
fn crash_with_git_changes_during_pending_peer_edit_merges_both() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    actor.persist()?;
    drop(actor);
    // Git rewrote the file while the peer's edit was still waiting to be written.
    std::fs::write(dir.path().join("shared"), "git\nline1\n")?;
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&RelativePath::new("shared"), "git\nline1\npeer\n");
    assert_eq!(
        std::fs::read(dir.path().join("shared"))?,
        b"git\nline1\npeer\n"
    );
    Ok(())
}


// A write that fails (here: the directory is read-only for a moment) must not make the next
// directory rescan read the missing file as "deleted on disk" and delete it from the shared
// document for every peer; once the disk is writable again the file must appear.
#[cfg(unix)]
#[tokio::test]
async fn failed_write_of_a_peers_file_does_not_delete_it_on_rescan() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let dir = tempdir()?;
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let path = RelativePath::new("from_peer");
    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o555))?;
    if std::fs::File::create(dir.path().join("probe")).is_ok() {
        return Ok(()); // permissions not enforced (e.g. running as root)
    }
    actor
        .crdt_doc
        .set_file(document::Content::String("peer text".into()), &path);
    actor.write_file(&path);
    assert!(!dir.path().join("from_peer").exists());
    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o755))?;
    actor.read_current_content_from_dir(false);
    assert!(
        actor.crdt_doc.file_exists(&path),
        "rescan deleted the peer's file from the shared document"
    );
    actor.handle_message(DocMessage::RescanFiles).await;
    assert_eq!(std::fs::read_to_string(dir.path().join("from_peer"))?, "peer text");
    Ok(())
}

#[test]
fn torn_incremental_append_does_not_break_restart() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    actor.persist()?;
    actor.crdt_doc.update_text("line1\npeer\nmore\n", &RelativePath::new("shared"));
    // Incremental append, then the machine dies after only part of it reached the disk.
    let doc = dir.path().join(".teamtypev/doc");
    let full = std::fs::read(&doc)?;
    actor.persist()?;
    let whole = std::fs::read(&doc)?;
    assert!(whole.len() > full.len());
    std::fs::write(&doc, &whole[..full.len() + (whole.len() - full.len()) / 2])?;
    drop(actor);
    let restarted = restarted_actor(&dir);
    let content = restarted.current_file_content(&RelativePath::new("shared"));
    assert!(content.is_some(), "recovered document lost the file");
    Ok(())
}

#[test]
fn kill_while_replacing_keeps_an_outside_write_made_since_the_last_read() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let path = RelativePath::new("shared");
    std::fs::write(dir.path().join("shared"), "line1\n")?;
    let mut actor = DocumentActor::setup_for_testing(&dir);
    actor.persist = true;
    actor.read_current_content_from_dir(true);
    actor.persist()?;
    actor.crdt_doc.update_text("line1\npeer\n", &path);
    actor.mark_pending([path.clone()]);
    actor.persist()?;
    // An outside program writes after the daemon's last read; the daemon swaps its bytes in and is
    // killed before it has merged the displaced ones.
    std::fs::write(dir.path().join("shared"), "outside\nline1\n")?;
    let prefix = displaced_prefix(&path);
    let (displaced, kept) = sandbox::replace_file_keeping(
        &actor.app_config.base_dir,
        &actor.absolute_path_for_file_path(&path),
        b"line1\npeer\n",
        Some(&prefix),
    )?;
    assert_eq!(displaced.as_deref(), Some(b"outside\nline1\n".as_slice()));
    assert!(kept.is_some());
    drop(actor);
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&path, "outside\nline1\npeer\n");
    assert_eq!(
        std::fs::read(dir.path().join("shared"))?,
        b"outside\nline1\npeer\n"
    );
    let left: Vec<_> = std::fs::read_dir(dir.path().join(".teamtypev"))?
        .flatten()
        .filter(|entry| entry.file_name().to_string_lossy().starts_with("displaced-"))
        .collect();
    assert!(left.is_empty());
    Ok(())
}

#[test]
fn normal_replacement_leaves_no_displaced_file() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    std::fs::write(dir.path().join("shared"), "outside\nline1\n")?;
    actor.try_write_file(&RelativePath::new("shared"))?;
    actor.assert_file_content(&RelativePath::new("shared"), "outside\nline1\npeer\n");
    let left = std::fs::read_dir(dir.path().join(".teamtypev"))?
        .flatten()
        .filter(|entry| entry.file_name().to_string_lossy().starts_with("displaced-"))
        .count();
    assert_eq!(left, 0);
    Ok(())
}

// A removal event that arrives while a write of that file is pending (it failed) is not a
// deletion by the user and must not delete the file from the shared document.
#[cfg(unix)]
#[tokio::test]
async fn removal_event_during_a_failed_write_does_not_delete_the_file() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let dir = tempdir()?;
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let path = RelativePath::new("from_peer");
    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o555))?;
    if std::fs::File::create(dir.path().join("probe")).is_ok() {
        return Ok(()); // permissions not enforced (e.g. running as root)
    }
    actor
        .crdt_doc
        .set_file(document::Content::String("peer text".into()), &path);
    actor.write_file(&path);
    actor.handle_watcher_event(&WatcherEvent {
        file_path: dir.path().join("from_peer"),
        event_type: WatcherEventType::Removed,
    });
    assert!(actor.crdt_doc.file_exists(&path));
    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o755))?;
    actor.handle_message(DocMessage::RescanFiles).await;
    assert_eq!(std::fs::read_to_string(dir.path().join("from_peer"))?, "peer text");
    Ok(())
}

// With no further file events, a failed write is still retried by the actor itself.
#[cfg(unix)]
#[tokio::test]
async fn failed_write_is_retried_without_any_event() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let dir = tempdir()?;
    let (_tx, doc_message_rx) = mpsc::channel(1);
    let (doc_changed_ping_tx, _rx) = broadcast::channel::<()>(1);
    let (ephemeral_message_tx, _erx) = broadcast::channel::<EphemeralMessage>(100);
    let mut actor = DocumentActor::new(
        doc_message_rx,
        doc_changed_ping_tx,
        ephemeral_message_tx,
        AppConfig {
            base_dir: dir.path().to_path_buf(),
            ..Default::default()
        },
        true,
        true,
        false,
    );
    let path = RelativePath::new("from_peer");
    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o555))?;
    if std::fs::File::create(dir.path().join("probe")).is_ok() {
        return Ok(());
    }
    actor
        .crdt_doc
        .set_file(document::Content::String("peer text".into()), &path);
    actor.write_file(&path);
    std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o755))?;
    let file = dir.path().join("from_peer");
    let _ = tokio::time::timeout(Duration::from_secs(5), async {
        // `_tx` stays alive, so `run` only returns when dropped by the timeout.
        let runner = actor.run();
        tokio::pin!(runner);
        tokio::select! {
            () = &mut runner => {}
            () = async { while !file.exists() { sleep(Duration::from_millis(10)).await } } => {}
        }
    })
    .await;
    assert_eq!(std::fs::read_to_string(&file)?, "peer text");
    Ok(())
}

#[test]
fn crash_before_removing_a_file_a_peer_deleted_does_not_resurrect_it() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let path = RelativePath::new("shared");
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    actor.crdt_doc.remove_file(&path);
    actor.persist()?;
    drop(actor);
    assert!(dir.path().join("shared").exists());
    let restarted = restarted_actor(&dir);
    assert!(restarted.current_file_content(&path).is_none());
    assert!(!dir.path().join("shared").exists());
    Ok(())
}

#[test]
fn crash_before_creating_a_file_a_peer_created_still_creates_it() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    let created = RelativePath::new("created");
    actor.crdt_doc.update_text("new\n", &created);
    actor.mark_pending([created.clone()]);
    actor.persist()?;
    drop(actor);
    assert!(!dir.path().join("created").exists());
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&created, "new\n");
    assert_eq!(std::fs::read(dir.path().join("created"))?, b"new\n");
    Ok(())
}

#[test]
fn crash_with_an_unsaved_editor_edit_keeps_the_disk_version_once() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let path = RelativePath::new("shared");
    std::fs::write(dir.path().join("shared"), "line1\n")?;
    let mut actor = DocumentActor::setup_for_testing(&dir);
    actor.persist = true;
    actor.read_current_content_from_dir(true);
    actor.files_open_in_editors.insert(path.clone());
    actor.save_files_open_in_editors();
    actor.crdt_doc.update_text("line1\neditor\n", &path);
    actor.persist()?;
    drop(actor);
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&path, "line1\n");
    assert_eq!(std::fs::read(dir.path().join("shared"))?, b"line1\n");
    Ok(())
}

#[test]
fn crash_after_merging_an_outside_edit_before_writing_keeps_it_once() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let path = RelativePath::new("shared");
    std::fs::write(dir.path().join("shared"), "line1\n")?;
    let mut actor = DocumentActor::setup_for_testing(&dir);
    actor.persist = true;
    actor.read_current_content_from_dir(true);
    actor.persist()?;
    std::fs::write(dir.path().join("shared"), "line1\nout\n")?;
    actor.file_created_or_changed(&path);
    actor.persist()?;
    drop(actor);
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&path, "line1\nout\n");
    assert_eq!(std::fs::read(dir.path().join("shared"))?, b"line1\nout\n");
    Ok(())
}

#[test]
fn finish_git_writes_every_deferred_edit_and_clears_the_records() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    let path = RelativePath::new("shared");
    assert!(actor.start_git(&[])?);
    actor.write_file(&path);
    assert_eq!(std::fs::read(dir.path().join("shared"))?, b"line1\n");
    actor.finish_git()?;
    assert_eq!(std::fs::read(dir.path().join("shared"))?, b"line1\npeer\n");
    assert!(actor.read_pending().is_empty());
    Ok(())
}

#[test]
fn staged_bytes_left_by_a_kill_before_the_swap_are_not_merged_as_an_outside_edit() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let path = RelativePath::new("shared");
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    actor.persist()?;
    let staged = dir
        .path()
        .join(".teamtypev")
        .join(format!("{}stage", displaced_prefix(&path)));
    std::fs::write(&staged, "line1\npeer\n")?;
    drop(actor);
    // Another program changed the file meanwhile, so the restart merges before it writes.
    std::fs::write(dir.path().join("shared"), "outside\nline1\n")?;
    let restarted = restarted_actor(&dir);
    restarted.assert_file_content(&path, "outside\nline1\npeer\n");
    assert!(!staged.exists());
    Ok(())
}

#[test]
fn skipping_a_write_that_is_already_on_disk_still_saves_the_document() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let path = RelativePath::new("shared");
    let mut actor = actor_with_pending_peer_edit(&dir)?;
    std::fs::write(dir.path().join("shared"), "line1\npeer\n")?;
    actor.try_write_file(&path)?;
    drop(actor);
    let saved = Document::load(&std::fs::read(dir.path().join(".teamtypev/doc"))?);
    assert_eq!(
        saved.current_file_content(&path),
        Some(&document::Content::String("line1\npeer\n".into()))
    );
    Ok(())
}

// An editor may send `open` for a file it already has open, without `close`. The daemon then
// replaces that file's OT session with a fresh one at revision 0 holding the editor's buffer and
// sends the catch-up edit as for a first open, so later edits apply to the shared text. (Daemon
// edits still in flight from the old session are the reopen hazard of
// `reopened_session_applies_stale_daemon_edit_unless_old_messages_are_drained`.)
// Verus model: daemon_proof (`open` on an owner).
#[tokio::test]
async fn open_of_an_already_open_file_restarts_its_session() -> Result<()> {
    let dir = setup_filesystem_for_testing();
    let mut actor = DocumentActor::setup_for_testing(&dir);
    let path = RelativePath::new("file1");
    let (uri, _reader) = open_test_editor(&mut actor, &path).await;
    let edit = |old: &str, new: &str, revision| EditorProtocolMessageFromEditor::Edit {
        uri: uri.clone(),
        revision,
        delta: crate::types::EditorTextDelta::try_from_delta(
            TextDelta::from(dissimilar::diff(old, new)),
            old,
        )
        .unwrap(),
    };
    actor
        .react_to_message_from_editor(1, &edit("content1", "Xcontent1", 0))
        .await
        .expect("edit");
    actor.assert_file_content(&path, "Xcontent1");
    // Open again with a stale buffer: the new session starts at that buffer and revision 0.
    actor
        .react_to_message_from_editor(
            1,
            &EditorProtocolMessageFromEditor::Open {
                uri: uri.clone(),
                content: "content1".into(),
                saves_file: false,
                daemon_writes: true,
            },
        )
        .await
        .expect("second open");
    actor.assert_file_content(&path, "Xcontent1");
    // An edit made before the editor received the catch-up edit is transformed against it.
    actor
        .react_to_message_from_editor(1, &edit("content1", "content1Y", 0))
        .await
        .expect("edit in the new session");
    actor.assert_file_content(&path, "Xcontent1Y");
    assert_eq!(
        std::fs::read_to_string(dir.path().join("file1"))?,
        "Xcontent1Y"
    );
    Ok(())
}
