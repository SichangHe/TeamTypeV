// SPDX-License-Identifier: AGPL-3.0-or-later

#![cfg(feature = "cli")]

use std::path::Path;
use std::process::{Command, Output, Stdio};
use std::{
    io::{BufRead, BufReader, Read, Write},
    os::unix::fs::PermissionsExt,
    os::unix::net::UnixListener,
    time::{Duration, Instant},
};

fn spawn_editor_listener(socket: &Path, document: teamtype::daemon::DocumentActorHandle) {
    static SOCKET_SETUP: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _guard = SOCKET_SETUP.lock().expect("socket setup lock");
    teamtype::editor::spawn_socket_listener(socket, document).expect("editor listener");
}

fn agent(directory: &Path, args: &[&str]) -> Output {
    std::fs::create_dir_all(directory.join(".teamtype")).expect("project metadata directory");
    let mut child = Command::new("sh")
        .args(["-c", "umask 022; exec \"$@\"", "teamtype-test"])
        .arg(env!("CARGO_BIN_EXE_teamtype"))
        .arg("--directory")
        .arg(directory)
        .args(args)
        .env_remove("TEAMTYPE_AGENT")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run agent command");
    let mut stdout = child.stdout.take().expect("stdout");
    let mut stderr = child.stderr.take().expect("stderr");
    let stdout = std::thread::spawn(move || {
        let mut bytes = vec![];
        stdout.read_to_end(&mut bytes).expect("read stdout");
        bytes
    });
    let stderr = std::thread::spawn(move || {
        let mut bytes = vec![];
        stderr.read_to_end(&mut bytes).expect("read stderr");
        bytes
    });
    let deadline = Instant::now() + Duration::from_secs(5);
    while child.try_wait().expect("agent status").is_none() {
        if Instant::now() >= deadline {
            child.kill().expect("stop timed-out agent");
            let output = child.wait_with_output().expect("reap timed-out agent");
            panic!("agent command timed out: {args:?}: {output:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    Output {
        status: child.wait().expect("agent exit"),
        stdout: stdout.join().expect("stdout reader"),
        stderr: stderr.join().expect("stderr reader"),
    }
}

fn successful(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("UTF-8 output")
}

#[test]
fn overlapping_edits_are_rejected() {
    let dir = tempfile::tempdir().expect("project");
    std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata");
    std::fs::write(dir.path().join("note.txt"), "aaa").expect("source");
    let output = agent(
        dir.path(),
        &[
            "agent-edit",
            "--file",
            "note.txt",
            "--old",
            "aa",
            "--new",
            "X",
        ],
    );
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("occurs 2 times"));
    assert_eq!(
        std::fs::read_to_string(dir.path().join("note.txt")).expect("source"),
        "aaa"
    );
}

#[test]
fn unsafe_snapshot_arguments_are_rejected() {
    let dir = tempfile::tempdir().expect("project");
    std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata");
    std::fs::write(dir.path().join("note.txt"), "aaa").expect("source");
    std::fs::write(dir.path().join("config"), "project\n").expect("project config");
    std::fs::write(dir.path().join(".teamtype/config"), "username=keep\n").expect("config");
    for args in [
        vec!["agent-read", "--agent", "..", "--file", "config"],
        vec!["agent-read", "--file", "../config"],
        vec!["agent-diff", "--agent", "../other"],
        vec![
            "agent-edit",
            "--agent",
            "..",
            "--file",
            "note.txt",
            "--old",
            "aaa",
            "--new",
            "changed",
        ],
    ] {
        assert!(!agent(dir.path(), &args).status.success(), "{args:?}");
    }
    assert_eq!(
        std::fs::read_to_string(dir.path().join(".teamtype/config")).expect("config"),
        "username=keep\n"
    );
    assert_eq!(
        std::fs::read_to_string(dir.path().join("note.txt")).expect("source"),
        "aaa"
    );
}

#[test]
fn snapshots_survive_file_directory_changes_and_long_paths() {
    let dir = tempfile::tempdir().expect("project");
    let a = dir.path().join("a");
    std::fs::write(&a, "parent\n").expect("parent file");
    successful(agent(dir.path(), &["agent-read", "--file", "a"]));
    std::fs::remove_file(&a).expect("remove parent");
    std::fs::create_dir(&a).expect("parent directory");
    std::fs::write(a.join("b"), "child\n").expect("child");
    successful(agent(dir.path(), &["agent-read", "--file", "a/b"]));
    std::fs::remove_dir_all(&a).expect("remove child layout");
    std::fs::write(&a, "new parent\n").expect("parent again");
    successful(agent(
        dir.path(),
        &[
            "agent-edit",
            "--file",
            "a",
            "--old",
            "new parent",
            "--new",
            "new parent",
        ],
    ));
    let file = format!("{}/note.txt", vec!["x".repeat(120); 20].join("/"));
    let path = dir.path().join(&file);
    std::fs::create_dir_all(path.parent().expect("parent")).expect("long directories");
    std::fs::write(&path, "long before\n").expect("long file");
    successful(agent(dir.path(), &["agent-read", "--file", &file]));
    std::fs::write(&path, "long after\n").expect("long change");
    assert!(
        successful(agent(dir.path(), &["agent-diff", "--file", &file]))
            .contains("-long before\n+long after\n")
    );
    assert!(successful(agent(dir.path(), &["agent-diff"])).contains(&file));
}

#[test]
fn standalone_snapshots_are_private_even_with_public_metadata_directory() {
    fn check(path: &Path) {
        for entry in std::fs::read_dir(path).expect("snapshot directory") {
            let path = entry.expect("entry").path();
            let metadata = path.metadata().expect("mode");
            assert_eq!(
                metadata.permissions().mode() & 0o077,
                0,
                "{}",
                path.display()
            );
            if metadata.is_dir() {
                check(&path);
            }
        }
    }
    let dir = tempfile::tempdir().expect("project");
    let metadata = dir.path().join(".teamtype");
    std::fs::create_dir(&metadata).expect("metadata");
    std::fs::set_permissions(&metadata, std::fs::Permissions::from_mode(0o755))
        .expect("public metadata");
    let source = dir.path().join("secret.txt");
    std::fs::write(&source, "secret\n").expect("source");
    std::fs::set_permissions(&source, std::fs::Permissions::from_mode(0o600))
        .expect("private source");
    successful(agent(dir.path(), &["agent-read", "--file", "secret.txt"]));
    check(&metadata);
}

#[test]
fn blocked_read_snapshots_only_the_bytes_printed() {
    let dir = tempfile::tempdir().expect("project");
    std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata");
    let file = dir.path().join("note.txt");
    let original = "original".repeat(100_000) + "\n";
    std::fs::write(&file, &original).expect("large source");
    let mut child = Command::new(env!("CARGO_BIN_EXE_teamtype"))
        .arg("--directory")
        .arg(dir.path())
        .args(["agent-read", "--file", "note.txt"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("agent read");
    let mut stdout = child.stdout.take().expect("stdout");
    let mut first = [0];
    stdout.read_exact(&mut first).expect("read started");
    std::fs::write(&file, "unseen\n").expect("concurrent update");
    let mut printed = first.to_vec();
    stdout.read_to_end(&mut printed).expect("drain stdout");
    assert!(child.wait().expect("agent exit").success());
    assert_eq!(printed, original.as_bytes());
    let diff = successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"]));
    assert!(diff.contains("+unseen\n"));
}

#[test]
fn crash_recovery_keeps_offline_saves_and_starts() {
    let dir = tempfile::tempdir().expect("project");
    let metadata = dir.path().join(".teamtype");
    std::fs::create_dir(&metadata).expect("metadata");
    let mut doc = teamtype::document::Document::default();
    doc.set_file(
        teamtype::document::Content::String("shared before crash\n".into()),
        &teamtype::path::RelativePath::new("note.txt"),
    );
    std::fs::write(metadata.join("doc"), doc.save()).expect("persisted document");
    std::fs::write(metadata.join("open-files"), "note.txt\n").expect("crash marker");
    std::fs::write(dir.path().join("note.txt"), "offline save\n").expect("new saved text");
    let mut child = Command::new(env!("CARGO_BIN_EXE_teamtype"))
        .arg("--directory")
        .arg(dir.path())
        .args(["share", "--no-join-code"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("restart daemon");
    // Give the daemon time to restore or rescan; it must keep running and keep the save.
    let deadline = Instant::now() + Duration::from_secs(5);
    while Instant::now() < deadline {
        assert!(
            child.try_wait().expect("daemon status").is_none(),
            "daemon stopped"
        );
        assert_eq!(
            std::fs::read_to_string(dir.path().join("note.txt")).expect("saved file"),
            "offline save\n"
        );
        std::thread::sleep(Duration::from_millis(50));
    }
    child.kill().expect("stop daemon");
    let output = child.wait_with_output().expect("daemon output");
    let log = String::from_utf8_lossy(&output.stdout) + String::from_utf8_lossy(&output.stderr);
    assert!(log.contains("keeping the version on disk"), "{log}");
}

#[tokio::test]
async fn crash_recovery_allows_matching_saved_text_without_rewriting_it() {
    let dir = tempfile::tempdir().expect("project");
    let metadata = dir.path().join(".teamtype");
    std::fs::create_dir(&metadata).expect("metadata");
    let mut doc = teamtype::document::Document::default();
    doc.set_file(
        teamtype::document::Content::String("shared\n".into()),
        &teamtype::path::RelativePath::new("note.txt"),
    );
    std::fs::write(metadata.join("doc"), doc.save()).expect("persisted history");
    std::fs::write(metadata.join("open-files"), "note.txt\n").expect("recovery list");
    std::fs::write(dir.path().join("note.txt"), "shared\n").expect("matching saved file");
    let modified = std::fs::metadata(dir.path().join("note.txt"))
        .expect("metadata")
        .modified()
        .expect("mtime");
    let config = teamtype::config::AppConfig {
        base_dir: dir.path().into(),
        ..teamtype::config::AppConfig::default()
    };
    let _document = teamtype::daemon::DocumentActorHandle::new(&config, false, true, true);
    assert_eq!(
        std::fs::read_to_string(metadata.join("open-files")).expect("cleared recovery list"),
        ""
    );
    assert_eq!(
        std::fs::metadata(dir.path().join("note.txt"))
            .expect("metadata")
            .modified()
            .expect("mtime"),
        modified
    );
}

#[test]
fn read_and_diff_keep_independent_snapshots_and_do_not_advance_on_diff() {
    let dir = tempfile::tempdir().expect("temporary project");
    std::fs::create_dir(dir.path().join("sub")).expect("nested files");
    let file = dir.path().join("sub/note.txt");
    std::fs::write(&file, "one\n").expect("initial file");
    assert_eq!(
        successful(agent(
            dir.path(),
            &["agent-read", "--file", "sub/note.txt", "--agent", "ann"]
        )),
        "one\n"
    );
    std::fs::write(&file, "two\n").expect("changed file");
    assert_eq!(
        successful(agent(
            dir.path(),
            &["agent-read", "--file", "sub/note.txt", "--agent", "bob"]
        )),
        "two\n"
    );
    let args = ["agent-diff", "--agent", "ann"];
    let diff = successful(agent(dir.path(), &args));
    assert_eq!(
        diff,
        "--- sub/note.txt (last read or written)\n+++ sub/note.txt (now)\n@@ -1 +1 @@\n-one\n+two\n"
    );
    assert_eq!(successful(agent(dir.path(), &args)), diff);
    assert_eq!(
        successful(agent(dir.path(), &["agent-diff", "--agent", "bob"])),
        ""
    );
    successful(agent(
        dir.path(),
        &["agent-read", "--file", "sub/note.txt", "--agent", "ann"],
    ));
    assert_eq!(successful(agent(dir.path(), &args)), "");
    std::fs::remove_file(&file).expect("delete tracked file");
    assert_eq!(
        successful(agent(dir.path(), &args)),
        "--- sub/note.txt (last read or written)\n+++ sub/note.txt (now)\n@@ -1 +0,0 @@\n-two\n"
    );
}

#[test]
fn explicit_diff_reports_missing_snapshot_and_filters_other_files() {
    let dir = tempfile::tempdir().expect("temporary project");
    for file in ["a.txt", "b.txt"] {
        std::fs::write(dir.path().join(file), "before\n").expect("initial file");
        successful(agent(dir.path(), &["agent-read", "--file", file]));
        std::fs::write(dir.path().join(file), "after\n").expect("changed file");
    }
    let diff = successful(agent(dir.path(), &["agent-diff", "--file", "a.txt"]));
    assert!(diff.contains("--- a.txt (last read or written)"));
    assert!(!diff.contains("b.txt"));
    assert_eq!(
        successful(agent(dir.path(), &["agent-diff", "--file", "missing.txt"])),
        "No snapshot of missing.txt for agent; use agent-read first.\n"
    );
}

#[test]
fn rejected_edits_preserve_file_and_snapshot() {
    let dir = tempfile::tempdir().expect("temporary project");
    let file = dir.path().join("note.txt");
    std::fs::write(&file, "old old\n").expect("initial file");
    successful(agent(dir.path(), &["agent-read", "--file", "note.txt"]));
    for (old, message) in [
        ("old", "occurs 2 times"),
        ("absent", "not in the file"),
        ("", "text to replace is empty"),
    ] {
        let output = agent(
            dir.path(),
            &[
                "agent-edit",
                "--file",
                "note.txt",
                "--old",
                old,
                "--new",
                "replacement",
            ],
        );
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains(message));
        assert_eq!(
            std::fs::read_to_string(&file).expect("unchanged file"),
            "old old\n"
        );
        assert_eq!(
            successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"])),
            ""
        );
    }
    let output = agent(
        dir.path(),
        &[
            "agent-edit",
            "--file",
            "missing.txt",
            "--old",
            "x",
            "--new",
            "y",
        ],
    );
    assert!(!output.status.success());
    assert!(!dir.path().join("missing.txt").exists());
    assert!(
        !dir.path()
            .join(".teamtype/agent-snapshots/agent/missing.txt")
            .exists()
    );
}

#[test]
fn unchanged_edit_updates_snapshot_without_daemon() {
    let dir = tempfile::tempdir().expect("temporary project");
    let file = dir.path().join("note.txt");
    std::fs::write(&file, "before\n").expect("initial file");
    successful(agent(dir.path(), &["agent-read", "--file", "note.txt"]));
    std::fs::write(&file, "after\n").expect("changed file");
    successful(agent(
        dir.path(),
        &[
            "agent-edit",
            "--file",
            "note.txt",
            "--old",
            "after",
            "--new",
            "after",
        ],
    ));
    assert_eq!(
        successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"])),
        ""
    );
    assert_eq!(
        std::fs::read_to_string(file).expect("unchanged file"),
        "after\n"
    );
}

#[test]
fn edit_refuses_daemon_content_that_changed_before_barrier() {
    let dir = tempfile::tempdir().expect("temporary project");
    std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata directory");
    std::fs::write(dir.path().join("note.txt"), "disk content\n").expect("initial file");
    successful(agent(dir.path(), &["agent-read", "--file", "note.txt"]));
    let listener = UnixListener::bind(dir.path().join(".teamtype/socket")).expect("daemon socket");
    listener.set_nonblocking(true).expect("nonblocking accept");
    let server = std::thread::spawn(move || {
        let deadline = Instant::now() + Duration::from_secs(5);
        let mut socket = loop {
            match listener.accept() {
                Ok((socket, _)) => break socket,
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    assert!(Instant::now() < deadline, "agent did not connect");
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(error) => panic!("agent connection failed: {error}"),
            }
        };
        socket
            .set_nonblocking(false)
            .expect("blocking protocol reads");
        socket
            .set_read_timeout(Some(Duration::from_secs(5)))
            .expect("socket timeout");
        let mut reader = BufReader::new(socket.try_clone().expect("read socket"));
        let mut line = String::new();
        reader.read_line(&mut line).expect("open request");
        let open: serde_json::Value = serde_json::from_str(&line).expect("open JSON");
        assert_eq!(open["method"], "open");
        assert_eq!(open["params"]["content"], "disk content\n");
        assert_eq!(open["params"]["savesFile"], false);
        line.clear();
        reader.read_line(&mut line).expect("barrier request");
        let barrier: serde_json::Value = serde_json::from_str(&line).expect("barrier JSON");
        assert_eq!(barrier["method"], "cursor");
        assert_eq!(barrier["params"]["ranges"], serde_json::json!([]));
        let changed = serde_json::json!({"jsonrpc": "2.0", "method": "edit", "params": {"uri": open["params"]["uri"], "revision": 0, "delta": []}});
        writeln!(socket, "{changed}").expect("unsaved edit notification");
        line.clear();
        assert_eq!(reader.read_line(&mut line).expect("agent disconnects"), 0);
    });
    let output = agent(
        dir.path(),
        &[
            "agent-edit",
            "--file",
            "note.txt",
            "--old",
            "disk",
            "--new",
            "replacement",
        ],
    );
    server.join().expect("protocol assertions");
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("file changed while editing, or an editor has unsaved changes")
    );
    assert_eq!(
        std::fs::read_to_string(dir.path().join("note.txt")).expect("unchanged disk content"),
        "disk content\n"
    );
    assert_eq!(
        successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"])),
        ""
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn outside_write_before_watcher_delivery_survives_an_editor_edit() {
    use teamtype::types::{RevisionedEditorTextDelta, RevisionedTextDelta};
    let dir = tempfile::tempdir().expect("project");
    std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata");
    let file = dir.path().join("note.txt");
    std::fs::write(&file, "base\n").expect("initial text");
    let config = teamtype::config::AppConfig {
        base_dir: dir.path().into(),
        ..Default::default()
    };
    let document = teamtype::daemon::DocumentActorHandle::new(&config, true, true, true);
    let socket = dir.path().join(".teamtype/socket");
    spawn_editor_listener(&socket, document);
    let mut editor = std::os::unix::net::UnixStream::connect(socket).expect("editor");
    editor
        .set_read_timeout(Some(Duration::from_secs(5)))
        .expect("timeout");
    let mut reader = BufReader::new(editor.try_clone().expect("reader"));
    let uri = format!("file://{}", file.display());
    writeln!(
        editor,
        "{}",
        serde_json::json!({"jsonrpc":"2.0", "id":1, "method":"open", "params":{
            "uri":uri, "content":"base\n", "daemonWrites":true
        }})
    )
    .expect("open");
    let mut line = String::new();
    reader.read_line(&mut line).expect("opened");
    assert!(
        serde_json::from_str::<serde_json::Value>(&line)
            .expect("response")
            .get("error")
            .is_none()
    );
    std::fs::write(&file, "base\noutside\n").expect("outside write without a watcher event");
    writeln!(editor, "{}", serde_json::json!({"jsonrpc":"2.0", "id":2, "method":"edit", "params":{
        "uri":uri, "revision":0, "delta":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},"replacement":"typed\n"}]
    }})).expect("type concurrently");
    writeln!(editor, "{}", serde_json::json!({"jsonrpc":"2.0", "id":3, "method":"cursor", "params":{"uri":uri,"ranges":[]}})).expect("barrier");
    let mut buffer = "typed\nbase\n".to_owned();
    loop {
        line.clear();
        assert!(reader.read_line(&mut line).expect("message") > 0);
        let message: serde_json::Value = serde_json::from_str(&line).expect("JSON");
        assert!(message.get("error").is_none(), "{message}");
        if message["id"] == 3 {
            break;
        }
        if message["method"] == "edit" && message["params"]["revision"] == 1 {
            let edit: RevisionedEditorTextDelta =
                serde_json::from_value(message["params"].clone()).expect("delta");
            buffer = RevisionedTextDelta::try_from_rev_ed_delta(edit, &buffer)
                .expect("convert delta")
                .delta
                .apply_to(&buffer)
                .expect("apply delta");
        }
    }
    assert_eq!(buffer, "typed\nbase\noutside\n");
    assert_eq!(std::fs::read_to_string(file).expect("disk"), buffer);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn daemon_owned_file_saves_the_agents_write_with_an_open_editor() {
    let dir = tempfile::tempdir().expect("project");
    std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata");
    let file = dir.path().join("note.txt");
    std::fs::write(&file, "hello\n").expect("initial text");
    let config = teamtype::config::AppConfig {
        base_dir: dir.path().into(),
        ..teamtype::config::AppConfig::default()
    };
    let document = teamtype::daemon::DocumentActorHandle::new(&config, true, true, true);
    let socket = dir.path().join(".teamtype/socket");
    spawn_editor_listener(&socket, document);
    let mut editor = std::os::unix::net::UnixStream::connect(socket).expect("editor connection");
    editor
        .set_read_timeout(Some(Duration::from_secs(5)))
        .expect("editor timeout");
    let open = serde_json::json!({"jsonrpc":"2.0", "id":1, "method":"open", "params":{
        "uri": format!("file://{}", file.display()), "content":"hello\n", "daemonWrites":true
    }});
    writeln!(editor, "{open}").expect("open file");
    let mut reader = BufReader::new(editor.try_clone().expect("editor reader"));
    let mut line = String::new();
    reader.read_line(&mut line).expect("open response");
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&line).expect("response")["id"],
        1
    );
    successful(agent(
        dir.path(),
        &[
            "agent-edit",
            "--file",
            "note.txt",
            "--old",
            "hello",
            "--new",
            "world",
        ],
    ));
    assert_eq!(
        std::fs::read_to_string(&file).expect("editor owns saves"),
        "world\n"
    );
    let diff = successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"]));
    assert_eq!(diff, "");
    assert_eq!(
        successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"])),
        ""
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn edit_through_document_daemon_persists_and_refreshes_snapshot() {
    let dir = tempfile::tempdir().expect("temporary project");
    std::fs::create_dir(dir.path().join(".teamtype")).expect("metadata directory");
    let file = dir.path().join("note.txt");
    std::fs::write(&file, "α before\nkeep\n").expect("initial file");
    successful(agent(dir.path(), &["agent-read", "--file", "note.txt"]));
    let config = teamtype::config::AppConfig {
        base_dir: dir.path().into(),
        ..teamtype::config::AppConfig::default()
    };
    let document = teamtype::daemon::DocumentActorHandle::new(&config, true, true, true);
    spawn_editor_listener(&dir.path().join(".teamtype/socket"), document);
    successful(agent(
        dir.path(),
        &[
            "agent-edit",
            "--file",
            "note.txt",
            "--old",
            "before",
            "--new",
            "after🙂",
        ],
    ));
    assert_eq!(
        std::fs::read_to_string(&file).expect("saved edit"),
        "α after🙂\nkeep\n"
    );
    assert_eq!(
        successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"])),
        ""
    );
    std::fs::write(&file, "α after🙂\nchanged\n").expect("later change");
    let diff = successful(agent(dir.path(), &["agent-diff", "--file", "note.txt"]));
    assert!(diff.contains("-keep\n+changed\n"), "{diff}");
    assert!(!diff.contains("before"), "{diff}");
}
