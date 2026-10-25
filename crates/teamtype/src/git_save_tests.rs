// SPDX-License-Identifier: AGPL-3.0-or-later

async fn test_editor_request(
    handle: &DocumentActorHandle,
    reader: &mut tokio::io::Lines<tokio::io::BufReader<UnixStream>>,
    method: &str,
    params: serde_json::Value,
) -> Result<serde_json::Value> {
    let message = crate::editor_protocol::IncomingMessage::from_jsonrpc(
        &serde_json::json!({"jsonrpc": "2.0", "id": 7, "method": method, "params": params})
            .to_string(),
    )
    .with_context(|| format!("Invalid {method} test request"))?;
    handle
        .send_message(crate::daemon::DocMessage::FromEditor(1, message))
        .await;
    timeout(Duration::from_secs(5), async {
        while let Some(line) = reader.next_line().await? {
            let response: serde_json::Value = serde_json::from_str(&line)?;
            if response.get("id") == Some(&serde_json::json!(7)) {
                return Ok(response);
            }
        }
        bail!("Editor disconnected")
    })
    .await?
}

async fn test_editor(
    handle: &DocumentActorHandle,
    path: &str,
    content: &str,
) -> Result<(tokio::io::Lines<tokio::io::BufReader<UnixStream>>, String)> {
    use tokio::io::AsyncBufReadExt;
    let (socket, reader) = UnixStream::pair()?;
    let (_, writer) = tokio::io::split(socket);
    handle
        .send_message(crate::daemon::DocMessage::NewEditorConnection(
            1,
            tokio_util::codec::FramedWrite::new(writer, crate::editor::OutgoingProtocolCodec),
        ))
        .await;
    let uri = crate::path::AbsolutePath::try_from(handle.base_dir().join(path))?
        .to_file_uri()
        .to_string();
    let mut reader = tokio::io::BufReader::new(reader).lines();
    let opened = test_editor_request(
        handle,
        &mut reader,
        "open",
        serde_json::json!({
            "uri": uri, "content": content, "savesFile": false, "daemonWrites": true,
        }),
    )
    .await?;
    assert!(opened.get("error").is_none(), "{opened}");
    Ok((reader, uri))
}

#[tokio::test]
async fn forwarded_git_retains_typing_and_rejects_saves_until_writer_stops() -> Result<()> {
    for cancel in [false, true] {
        let root = tempfile::tempdir()?;
        std::fs::create_dir(root.path().join(".teamtype"))?;
        let repository = git2::Repository::init(root.path())?;
        repository.config()?.set_str(
            "alias.paused-writer",
            concat!(
                "!f() { exec 3>text; printf 'content1\\noutside-first\\n' >&3; ",
                "printf ready; read release; printf 'outside-second\\n' >&3; }; f"
            ),
        )?;
        std::fs::write(root.path().join("text"), "content1")?;
        let config = crate::config::AppConfig {
            base_dir: root.path().to_path_buf(),
            ..Default::default()
        };
        let handle = DocumentActorHandle::new(&config, true, true, false);
        let (mut editor, uri) = test_editor(&handle, "text", "content1").await?;
        start(handle.clone())?;
        let (input, mut writer) = Input::new()?;
        let (response, mut responses) = mpsc::channel(8);
        handle
            .git
            .enqueue(Job {
                request: Request {
                    id: 1,
                    args: vec![b"paused-writer".to_vec()],
                    cwd: vec![],
                    heads: handle.git_heads().await,
                    terminal: None,
                },
                input,
                response,
            })
            .await?;
        timeout(Duration::from_secs(5), async {
            loop {
                match responses.recv().await {
                    Some(Response::Stdout(bytes)) if bytes == b"ready" => return Ok(()),
                    Some(Response::Error(error)) => bail!("{error}"),
                    None => bail!("Git stopped before opening its file"),
                    _ => {}
                }
            }
        })
        .await??;
        assert!(
            handle.git_ready(vec![]).await?,
            "An earlier command's exit must not wait for the running command"
        );
        handle
            .send_message(crate::daemon::DocMessage::RescanFiles)
            .await;
        let edited = test_editor_request(
            &handle,
            &mut editor,
            "edit",
            serde_json::json!({
                "uri": uri, "revision": 0, "delta": test_edit_delta("content1", "typed\ncontent1")
            }),
        )
        .await?;
        assert!(edited.get("error").is_none(), "{edited}");
        let saved = test_editor_request(
            &handle,
            &mut editor,
            "save",
            serde_json::json!({"uri": uri}),
        )
        .await?;
        let disk_during_git = std::fs::read_to_string(root.path().join("text"))?;
        let shared_during_git = handle.content().await;
        if cancel {
            drop(responses);
        } else {
            writer.write(b"go\n")?;
            writer.write(b"")?;
            timeout(Duration::from_secs(5), async {
                loop {
                    match responses.recv().await {
                        Some(Response::Exit(code, _)) => {
                            assert_eq!(code, 0);
                            return Ok(());
                        }
                        Some(Response::Error(error)) => bail!("{error}"),
                        None => bail!("Git exited without a result"),
                        _ => {}
                    }
                }
            })
            .await??;
        }
        assert_eq!(
            test_forwarded_git(&handle, &["status", "--porcelain"]).await?,
            0
        );
        let expected = if cancel {
            "typed\ncontent1\noutside-first\n"
        } else {
            "typed\ncontent1\noutside-first\noutside-second\n"
        };
        assert_eq!(std::fs::read_to_string(root.path().join("text"))?, expected);
        assert_eq!(disk_during_git, "content1\noutside-first\n");
        assert_eq!(
            shared_during_git,
            Some(crate::document::Content::String("typed\ncontent1".into()))
        );
        assert!(
            saved["error"]["message"]
                .as_str()
                .is_some_and(|s| s.contains("retry saving")),
            "{saved}"
        );
        assert_eq!(
            handle.content().await,
            Some(crate::document::Content::String(expected.into()))
        );
        let saved = test_editor_request(
            &handle,
            &mut editor,
            "save",
            serde_json::json!({"uri": uri}),
        )
        .await?;
        assert!(saved.get("error").is_none(), "{saved}");
        assert_eq!(std::fs::read_to_string(root.path().join("text"))?, expected);
    }
    Ok(())
}

async fn test_forwarded_git(handle: &DocumentActorHandle, args: &[&str]) -> Result<i32> {
    let (input, mut writer) = Input::new()?;
    writer.write(b"")?;
    let (response, mut responses) = mpsc::channel(8);
    handle
        .git
        .enqueue(Job {
            request: Request {
                id: 2,
                args: args.iter().map(|arg| arg.as_bytes().to_vec()).collect(),
                cwd: vec![],
                heads: handle.git_heads().await,
                terminal: None,
            },
            input,
            response,
        })
        .await?;
    timeout(Duration::from_secs(5), async {
        loop {
            match responses.recv().await {
                Some(Response::Exit(code, _)) => return Ok(code),
                Some(Response::Error(error)) => bail!("{error}"),
                None => bail!("Git exited without a result"),
                _ => {}
            }
        }
    })
    .await?
}

#[tokio::test]
async fn checkout_refuses_saved_typing_but_explicit_restore_deletes_it() -> Result<()> {
    let root = tempfile::tempdir()?;
    std::fs::create_dir(root.path().join(".teamtype"))?;
    let repository = git2::Repository::init(root.path())?;
    repository.set_head("refs/heads/base")?;
    repository.config()?.set_str("user.name", "Test")?;
    repository
        .config()?
        .set_str("user.email", "test@example.test")?;
    std::fs::write(root.path().join("text"), "content1")?;
    for args in [
        vec!["add", "text"],
        vec!["commit", "-qm", "base"],
        vec!["checkout", "-qb", "other"],
    ] {
        let output = Command::new(git_program()?)
            .args(args)
            .current_dir(root.path())
            .output()
            .await?;
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    std::fs::write(root.path().join("text"), "other branch")?;
    for args in [vec!["commit", "-qam", "other"], vec!["checkout", "base"]] {
        let output = Command::new(git_program()?)
            .args(args)
            .current_dir(root.path())
            .output()
            .await?;
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let config = crate::config::AppConfig {
        base_dir: root.path().to_path_buf(),
        ..Default::default()
    };
    let handle = DocumentActorHandle::new(&config, true, true, false);
    let (mut editor, uri) = test_editor(&handle, "text", "content1").await?;
    start(handle.clone())?;
    let edited = test_editor_request(
        &handle,
        &mut editor,
        "edit",
        serde_json::json!({
            "uri": uri, "revision": 0, "delta": test_edit_delta("content1", "typed\ncontent1")
        }),
    )
    .await?;
    assert!(edited.get("error").is_none(), "{edited}");
    let saved = test_editor_request(
        &handle,
        &mut editor,
        "save",
        serde_json::json!({"uri": uri}),
    )
    .await?;
    assert!(saved.get("error").is_none(), "{saved}");
    assert_ne!(
        test_forwarded_git(&handle, &["checkout", "other"]).await?,
        0
    );
    assert_eq!(
        std::fs::read_to_string(root.path().join("text"))?,
        "typed\ncontent1"
    );
    assert_eq!(
        handle.content().await,
        Some(crate::document::Content::String("typed\ncontent1".into()))
    );
    assert_eq!(
        test_forwarded_git(&handle, &["checkout", "--", "text"]).await?,
        0
    );
    assert_eq!(
        handle.content().await,
        Some(crate::document::Content::String("content1".into()))
    );
    let saved = test_editor_request(
        &handle,
        &mut editor,
        "save",
        serde_json::json!({"uri": uri}),
    )
    .await?;
    assert!(saved.get("error").is_none(), "{saved}");
    assert_eq!(
        std::fs::read_to_string(root.path().join("text"))?,
        "content1"
    );
    Ok(())
}

fn test_edit_delta(before: &str, after: &str) -> serde_json::Value {
    assert!(!before.contains('\n'));
    serde_json::json!([{
        "range": {"start": {"line": 0, "character": 0},
                  "end": {"line": 0, "character": before.chars().count()}},
        "replacement": after
    }])
}

#[tokio::test]
async fn forwarded_git_waits_for_background_writers_before_reconciling() -> Result<()> {
    let root = tempfile::tempdir()?;
    std::fs::create_dir(root.path().join(".teamtype"))?;
    let repository = git2::Repository::init(root.path())?;
    repository.config()?.set_str(
        "alias.background-writer",
        concat!(
            "!f() { (trap '' TERM; exec 3>>text; touch .git/writer-ready; ",
            "sleep 0.2; printf '\\nbackground' >&3; sleep 30) </dev/null >/dev/null 2>&1 & ",
            "while test ! -f .git/writer-ready; do sleep 0.01; done; }; f"
        ),
    )?;
    std::fs::write(root.path().join("text"), "content1")?;
    let config = crate::config::AppConfig {
        base_dir: root.path().to_path_buf(),
        ..Default::default()
    };
    let handle = DocumentActorHandle::new(&config, true, true, false);
    let (mut editor, uri) = test_editor(&handle, "text", "content1").await?;
    start(handle.clone())?;
    assert_eq!(
        test_forwarded_git(&handle, &["background-writer"]).await?,
        0
    );
    assert_eq!(
        handle.content().await,
        Some(crate::document::Content::String(
            "content1\nbackground".into()
        ))
    );
    let saved = test_editor_request(
        &handle,
        &mut editor,
        "save",
        serde_json::json!({"uri": uri}),
    )
    .await?;
    assert!(saved.get("error").is_none(), "{saved}");
    assert_eq!(
        std::fs::read_to_string(root.path().join("text"))?,
        "content1\nbackground"
    );
    Ok(())
}
