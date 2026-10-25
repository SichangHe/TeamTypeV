// SPDX-License-Identifier: AGPL-3.0-or-later

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
    std::fs::remove_dir_all(dir.path().join(".teamtype"))?;
    std::fs::write(dir.path().join(".teamtype"), b"occupied")?;
    let save = EditorProtocolMessageFromEditor::Save { uri };
    assert!(actor.react_to_message_from_editor(1, &save).await.is_err());
    assert!(actor.flush_git_files().is_err());
    actor.assert_file_content(&path, "unsaved typing");
    assert_eq!(std::fs::read(dir.path().join("file1"))?, b"content1");
    std::fs::remove_file(dir.path().join(".teamtype"))?;
    actor
        .react_to_message_from_editor(1, &save)
        .await
        .expect("retry save");
    assert_eq!(std::fs::read(dir.path().join("file1"))?, b"unsaved typing");
    let recovered = Document::load(&std::fs::read(dir.path().join(".teamtype/doc"))?);
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
