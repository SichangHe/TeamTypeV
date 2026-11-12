// SPDX-License-Identifier: AGPL-3.0-or-later

// Randomized interleavings of several peers, each with a daemon actor, a directory and editor
// clients, with in-flight messages in every direction. Editor clients follow the VS Code
// plugin's revision rules. After everything is delivered, all copies of every file must agree.

use rand::{RngExt, SeedableRng, rngs::StdRng};
use std::collections::VecDeque;

use crate::editor_protocol::JSONRPCId;
use crate::document::Content;
use crate::types::EditorTextDelta;

/// Applies simultaneous edits (all ranges refer to the original text), like an editor does.
fn apply_editor_delta(text: &str, delta: &EditorTextDelta) -> String {
    let chars: Vec<char> = text.chars().collect();
    let mut ops: Vec<(usize, usize, &str)> = delta
        .0
        .iter()
        .map(|op| {
            let (start, len) = op.range.as_relative(text).expect("range fits the editor buffer");
            (start, len, op.replacement.as_str())
        })
        .collect();
    ops.sort_by_key(|(start, _, _)| *start);
    let mut out = String::new();
    let mut at = 0;
    for (start, len, replacement) in ops {
        assert!(start >= at, "overlapping edits");
        out.extend(&chars[at..start]);
        out.push_str(replacement);
        at = start + len;
    }
    out.extend(&chars[at..]);
    out
}

/// The URI an editor plugin sends: every byte but `/` and unreserved characters percent-escaped
/// (what Neovim's `vim.uri_from_bufnr` gives, with lowercase hex).
fn plugin_uri(path: &AbsolutePath) -> String {
    use std::os::unix::ffi::OsStrExt;
    let escaped: String = Path::new(path.as_ref() as &Path)
        .as_os_str()
        .as_bytes()
        .iter()
        .map(|&b| match b {
            b'/' | b'-' | b'.' | b'_' | b'~' => (b as char).to_string(),
            _ if b.is_ascii_alphanumeric() => (b as char).to_string(),
            _ => format!("%{b:02x}"),
        })
        .collect();
    format!("file://{escaped}")
}

struct EditorClient {
    uri: String,
    reader: tokio::net::UnixStream,
    pending_read: Vec<u8>,
    buffer: String,
    /// Daemon edits applied / edits sent, as in the plugin's `Revision`.
    rev_daemon: usize,
    rev_editor: usize,
    inbox: VecDeque<(usize, EditorTextDelta)>,
    to_daemon: VecDeque<(usize, EditorTextDelta)>,
    next_request: usize,
}

struct Peer {
    dir: TempDir,
    actor: DocumentActor,
    editors: [Option<EditorClient>; 2],
    /// Watcher events not yet delivered.
    watcher: VecDeque<WatcherEventType>,
}

#[expect(clippy::struct_excessive_bools)]
struct World {
    peers: Vec<Peer>,
    states: Vec<Vec<SyncState>>,
    wire: Vec<Vec<VecDeque<AutomergeSyncMessage>>>,
    rng: StdRng,
    path: RelativePath,
    name: String,
    trace: Vec<String>,
    disk_writes: bool,
    replace: bool,
    unsettled: bool,
    verbose: bool,
    violation: Option<String>,
}

fn peer_actor(dir: &TempDir, is_host: bool) -> DocumentActor {
    let (_tx, rx) = mpsc::channel(1);
    let (ping, _r) = broadcast::channel::<()>(1);
    let (eph, _e) = broadcast::channel::<EphemeralMessage>(100);
    DocumentActor::new(
        rx,
        ping,
        eph,
        AppConfig {
            base_dir: dir.path().to_path_buf(),
            ..Default::default()
        },
        true,
        is_host,
        false,
    )
}

impl World {
    async fn new(seed: u64, peers: usize) -> Self {
        Self::named(seed, peers, "a").await
    }

    /// Like `new`, with the one shared file called `name`.
    async fn named(seed: u64, peers: usize, name: &str) -> Self {
        let path = RelativePath::new(name);
        let mut ps = vec![];
        for i in 0..peers {
            let dir = tempdir().unwrap();
            if i == 0 {
                std::fs::write(dir.path().join(name), "one\ntwo\nthree\n").unwrap();
            }
            let actor = peer_actor(&dir, i == 0);
            ps.push(Peer {
                dir,
                actor,
                editors: [None, None],
                watcher: VecDeque::new(),
            });
        }
        let mut w = Self {
            states: vec![vec![SyncState::new(); peers]; peers],
            wire: vec![vec![VecDeque::new(); peers]; peers],
            peers: ps,
            rng: StdRng::seed_from_u64(seed),
            path,
            name: name.to_string(),
            trace: vec![],
            disk_writes: false,
            replace: false,
            unsettled: false,
            verbose: false,
            violation: None,
        };
        w.sync_all().await;
        w
    }

    /// Records the first moment a daemon's file cache stops matching its CRDT.
    fn verify_cache(&mut self, after: &str) {
        if self.violation.is_some() {
            return;
        }
        for p in 0..self.peers.len() {
            let actor = &mut self.peers[p].actor;
            let cache = actor.current_file_content(&self.path).cloned();
            let real = Document::load(&actor.crdt_doc.save())
                .current_file_content(&self.path)
                .cloned();
            if cache != real {
                self.violation = Some(format!(
                    "after {after}: peer {p} cache {cache:?} != crdt {real:?}"
                ));
                return;
            }
        }
    }

    async fn gen_sync(&mut self, i: usize, j: usize) {
        let (tx, rx) = oneshot::channel();
        let state = std::mem::replace(&mut self.states[i][j], SyncState::new());
        self.peers[i]
            .actor
            .handle_message(DocMessage::GenerateSyncMessage {
                state,
                response_tx: tx,
            })
            .await;
        let (state, msg) = rx.await.unwrap();
        self.states[i][j] = state;
        if let Some(msg) = msg {
            self.wire[i][j].push_back(msg);
        }
    }

    async fn deliver(&mut self, i: usize, j: usize) {
        let Some(message) = self.wire[i][j].pop_front() else {
            return;
        };
        let (tx, rx) = oneshot::channel();
        let h0 = self.peers[j].actor.crdt_doc.get_heads().len();
        let c0 = self.peers[j].actor.current_file_content(&self.path).cloned();
        let state = std::mem::replace(&mut self.states[j][i], SyncState::new());
        self.peers[j]
            .actor
            .handle_message(DocMessage::ReceiveSyncMessage {
                message,
                state,
                response_tx: tx,
            })
            .await;
        self.states[j][i] = rx.await.unwrap();
        self.verify_cache(&format!("deliver {i}->{j}"));
        if self.verbose {
            let c1 = self.peers[j].actor.current_file_content(&self.path).cloned();
            let h1 = self.peers[j].actor.crdt_doc.get_heads();
            self.trace.push(format!("  deliver {i}->{j}: heads {h0}->{} {:?} crdt {c0:?} -> {c1:?}", h1.len(), &h1[0].to_string()[..6]));
        }
    }

    async fn sync_all(&mut self) {
        self.sync_all_rounds(200).await;
    }

    async fn sync_all_rounds(&mut self, rounds: usize) {
        let n = self.peers.len();
        for _ in 0..rounds {
            let mut idle = true;
            for i in 0..n {
                for j in 0..n {
                    if i == j {
                        continue;
                    }
                    self.gen_sync(i, j).await;
                    if !self.wire[i][j].is_empty() {
                        idle = false;
                        self.deliver(i, j).await;
                    }
                }
            }
            if idle {
                return;
            }
        }
        if rounds > 1 {
            self.unsettled = true;
        }
    }

    async fn pull(&mut self, p: usize, e: usize) {
        let Some(ed) = self.peers[p].editors[e].as_mut() else {
            return;
        };
        let mut buf = vec![0u8; 65536];
        loop {
            // Let the runtime register readiness before the non-blocking read.
            if tokio::time::timeout(Duration::from_millis(2), ed.reader.readable())
                .await
                .is_err()
            {
                break;
            }
            match ed.reader.try_read(&mut buf) {
                Ok(0) => break,
                Ok(n) => ed.pending_read.extend_from_slice(&buf[..n]),
                Err(_) => break,
            }
        }
        while let Some(pos) = ed.pending_read.iter().position(|b| *b == b'\n') {
            let line: Vec<u8> = ed.pending_read.drain(..=pos).collect();
            if let Ok(EditorProtocolMessageToEditor::Edit {
                revision, delta, ..
            }) = serde_json::from_slice::<EditorProtocolMessageToEditor>(&line)
            {
                ed.inbox.push_back((revision, delta));
            }
        }
    }

    async fn open_editor(&mut self, p: usize, e: usize) {
        if self.peers[p].editors[e].is_some() || !self.peers[p].dir.path().join(&self.name).exists() {
            return;
        }
        let path = self.path.clone();
        let actor = &mut self.peers[p].actor;
        let uri = plugin_uri(&actor.absolute_path_for_file_path(&path));
        let (stream, reader) = tokio::net::UnixStream::pair().unwrap();
        let (_, writer) = tokio::io::split(stream);
        actor.editor_connections.insert(
            e + 1,
            (
                EditorConnection::new("t".into(), actor.app_config.clone()),
                tokio_util::codec::FramedWrite::new(writer, editor::OutgoingProtocolCodec),
            ),
        );
        // The editor reads the file, then opens it. As in the plugin, it opens with the content
        // it read.
        let content = std::fs::read_to_string(self.peers[p].dir.path().join(&self.name))
            .unwrap_or_default();
        self.trace.push(format!("open {p} with {content:?}"));
        let id = 0;
        self.peers[p]
            .actor
            .handle_message(DocMessage::FromEditor(
                e + 1,
                IncomingMessage::Request {
                    id: JSONRPCId::Usize(id),
                    payload: EditorProtocolMessageFromEditor::Open {
                        uri: uri.clone(),
                        content: content.clone(),
                        saves_file: false,
                        daemon_writes: true,
                    },
                },
            ))
            .await;
        self.peers[p].editors[e] = Some(EditorClient {
            uri,
            reader,
            pending_read: vec![],
            buffer: content,
            rev_daemon: 0,
            rev_editor: 0,
            inbox: VecDeque::new(),
            to_daemon: VecDeque::new(),
            next_request: 1,
        });
        // Messages sent while handling the open belong to the new editor.
        self.pull(p, e).await;
    }

    fn random_text(&mut self) -> String {
        let n = self.rng.random_range(0..4);
        self.random_chars(n)
    }

    fn random_chars(&mut self, n: usize) -> String {
        repeat_with(|| ["x", "y", "\n", "é", "🥕"][self.rng.random_range(0..5)])
            .take(n)
            .collect()
    }

    fn local_edit(&mut self, p: usize, e: usize) {
        let Some(len) = self.peers[p]
            .editors[e]
            .as_ref()
            .map(|ed| ed.buffer.chars().count())
        else {
            return;
        };
        let at = self.rng.random_range(0..=len);
        let del = self.rng.random_range(0..=(len - at).min(3));
        let n = self.rng.random_range(0..4);
        let ins = self.random_chars(n);
        let ed = self.peers[p].editors[e].as_mut().expect("checked above");
        let mut delta = TextDelta::default();
        delta.retain(at);
        if del > 0 {
            delta.delete(del);
        } else {
            delta.insert(&ins);
        }
        let mut ed_delta = EditorTextDelta::try_from_delta(delta, &ed.buffer).unwrap();
        if del > 0 {
            ed_delta.0[0].replacement = ins.clone();
        }
        ed.buffer = apply_editor_delta(&ed.buffer, &ed_delta);
        ed.to_daemon.push_back((ed.rev_daemon, ed_delta));
        ed.rev_editor += 1;
        self.trace.push(format!("edit {p} at {at} del {del} ins {ins:?}"));
    }

    async fn send_to_daemon(&mut self, p: usize, e: usize) {
        let Some(ed) = self.peers[p].editors[e].as_mut() else {
            return;
        };
        let Some((revision, delta)) = ed.to_daemon.pop_front() else {
            return;
        };
        let id = ed.next_request;
        ed.next_request += 1;
        let uri = ed.uri.clone();
        self.trace.push(format!("deliver edit {p} rev {revision}"));
        self.peers[p]
            .actor
            .handle_message(DocMessage::FromEditor(
                e + 1,
                IncomingMessage::Request {
                    id: JSONRPCId::Usize(id),
                    payload: EditorProtocolMessageFromEditor::Edit {
                        uri,
                        revision,
                        delta,
                    },
                },
            ))
            .await;
    }

    fn apply_one_inbox(&mut self, p: usize, e: usize) {
        let Some(ed) = self.peers[p].editors[e].as_mut() else {
            return;
        };
        let Some((revision, delta)) = ed.inbox.pop_front() else {
            return;
        };
        if revision != ed.rev_editor {
            self.trace.push(format!("editor {p} ignores rev {revision}"));
            return;
        }
        ed.buffer = apply_editor_delta(&ed.buffer, &delta);
        ed.rev_daemon += 1;
        self.trace.push(format!("editor {p} applies rev {revision}"));
    }

    async fn disk_write(&mut self, p: usize) {
        let text = self.random_text();
        let file = self.peers[p].dir.path().join(&self.name);
        let old = std::fs::read_to_string(&file).unwrap_or_default();
        let new = if self.rng.random_bool(0.5) {
            format!("{old}{text}")
        } else {
            format!("{text}{old}")
        };
        std::fs::write(&file, &new).unwrap();
        self.trace.push(format!("disk write {p}: {new:?}"));
        self.peers[p].watcher.push_back(WatcherEventType::Changed);
    }

    fn disk_remove(&mut self, p: usize) {
        let file = self.peers[p].dir.path().join(&self.name);
        if std::fs::remove_file(&file).is_ok() {
            self.trace.push(format!("disk remove {p}"));
            self.peers[p].watcher.push_back(WatcherEventType::Removed);
        }
    }

    fn disk_create(&mut self, p: usize) {
        let file = self.peers[p].dir.path().join(&self.name);
        if !file.exists() {
            let text = self.random_text();
            self.trace.push(format!("disk create {p}: {text:?}"));
            std::fs::write(&file, text).unwrap();
            self.peers[p].watcher.push_back(WatcherEventType::Created);
        }
    }

    /// The file is deleted and written again, as an editor-less tool or `git checkout` does:
    /// the daemon sees the removal first, so the shared file gets a new text (or bytes) object.
    async fn disk_replace(&mut self, p: usize, binary: bool) {
        let file = self.peers[p].dir.path().join("a");
        if std::fs::remove_file(&file).is_ok() {
            self.fire(p, WatcherEventType::Removed).await;
        }
        let content: Vec<u8> = if binary {
            vec![0xff, 0xfe, self.rng.random_range(0..=255)]
        } else {
            self.random_text().into_bytes()
        };
        self.trace.push(format!("replace {p} with {content:?}"));
        std::fs::write(&file, content).unwrap();
        if self.rng.random_bool(0.7) {
            self.fire(p, WatcherEventType::Created).await;
        } else {
            self.peers[p].watcher.push_back(WatcherEventType::Created);
        }
    }

    async fn fire(&mut self, p: usize, event_type: WatcherEventType) {
        let file_path = self.peers[p].dir.path().join("a");
        self.peers[p]
            .actor
            .handle_message(DocMessage::FromWatcher(WatcherEvent {
                file_path,
                event_type,
            }))
            .await;
        self.verify_cache("fire");
    }

    async fn close_editor(&mut self, p: usize, e: usize) {
        let Some(ed) = self.peers[p].editors[e].take() else {
            return;
        };
        self.trace.push(format!("close {p}"));
        self.peers[p]
            .actor
            .handle_message(DocMessage::FromEditor(
                e + 1,
                IncomingMessage::Request {
                    id: JSONRPCId::Usize(9999),
                    payload: EditorProtocolMessageFromEditor::Close { uri: ed.uri },
                },
            ))
            .await;
        self.peers[p].actor.editor_connections.remove(&(e + 1));
    }

    async fn watcher(&mut self, p: usize) {
        let Some(kind) = self.peers[p].watcher.pop_front() else {
            return;
        };
        let file_path = self.peers[p].dir.path().join(&self.name);
        self.trace.push(format!("watcher {p}"));
        self.peers[p]
            .actor
            .handle_message(DocMessage::FromWatcher(WatcherEvent {
                file_path,
                event_type: kind,
            }))
            .await;
        self.verify_cache("watcher");
    }

    async fn step(&mut self) {
        let n = self.peers.len();
        let p = self.rng.random_range(0..n);
        let e = self.rng.random_range(0..2);
        match self.rng.random_range(0..18) {
            0 => self.open_editor(p, e).await,
            1..=3 => self.local_edit(p, e),
            4 => self.send_to_daemon(p, e).await,
            5 => {
                self.pull(p, e).await;
                self.apply_one_inbox(p, e);
            }
            6 | 7 => {
                let q = self.rng.random_range(0..n);
                if q != p {
                    self.gen_sync(p, q).await;
                }
            }
            8 | 9 => {
                let q = self.rng.random_range(0..n);
                if q != p {
                    self.trace.push(format!("sync msg {p}->{q}"));
                    self.deliver(p, q).await;
                }
            }
            10 if self.disk_writes => self.disk_write(p).await,
            11 if self.disk_writes => self.watcher(p).await,
            12 if self.disk_writes => self.disk_remove(p),
            13 if self.disk_writes => self.disk_create(p),
            14 if self.disk_writes => self.close_editor(p, e).await,
            15 | 16 if self.replace => {
                let binary = self.rng.random_range(0..4) == 0;
                self.disk_replace(p, binary).await;
            }
            _ => {}
        }
        self.verify_cache(&format!("step {}", self.trace.last().cloned().unwrap_or_default()));
        self.check_inside();
    }

    /// Between actor messages (`disk_edits` is drained), every file an editor connection has
    /// open has the daemon's shared text as its OT server text.
    fn check_inside(&mut self) {
        if self.violation.is_some() {
            return;
        }
        for p in 0..self.peers.len() {
            let actor = &self.peers[p].actor;
            for (id, (conn, _)) in &actor.editor_connections {
                let Some(server) = conn.server_text(&self.path) else {
                    continue;
                };
                let shared = actor.current_file_content(&self.path);
                if shared != Some(&Content::String(server.to_string())) {
                    self.violation = Some(format!(
                        "inside_ok: peer {p} editor {id} server {server:?} != shared {shared:?}"
                    ));
                    return;
                }
            }
        }
    }

    async fn quiesce(&mut self) {
        for _ in 0..500 {
            let mut busy = false;
            for p in 0..self.peers.len() {
                if !self.peers[p].watcher.is_empty() {
                    self.watcher(p).await;
                    busy = true;
                }
                for e in 0..2 {
                    self.pull(p, e).await;
                    if self.peers[p].editors[e]
                        .as_ref()
                        .is_some_and(|c| !c.to_daemon.is_empty())
                    {
                        self.send_to_daemon(p, e).await;
                        busy = true;
                    }
                    self.pull(p, e).await;
                    while self.peers[p].editors[e]
                        .as_ref()
                        .is_some_and(|c| !c.inbox.is_empty())
                    {
                        self.apply_one_inbox(p, e);
                        busy = true;
                    }
                    self.check_inside();
                }
            }
            let before: Vec<_> = (0..self.peers.len())
                .map(|p| self.peers[p].actor.current_file_content(&self.path).cloned())
                .collect();
            self.sync_all().await;
            if self.unsettled {
                return;
            }
            let after: Vec<_> = (0..self.peers.len())
                .map(|p| self.peers[p].actor.current_file_content(&self.path).cloned())
                .collect();
            if before != after {
                busy = true;
            }
            if !busy {
                return;
            }
        }
        panic!("did not quiesce");
    }

    fn check(&mut self) -> Result<(), String> {
        let n = self.peers.len();
        let reference = self.peers[0].actor.current_file_content(&self.path).cloned();
        for p in 0..n {
            let actor = &mut self.peers[p].actor;
            let cache = actor.current_file_content(&self.path).cloned();
            // The cache must equal what the CRDT really holds.
            let bytes = actor.crdt_doc.save();
            let fresh = Document::load(&bytes);
            let real = fresh.current_file_content(&self.path).cloned();
            if cache != real {
                return Err(format!("peer {p}: cache {cache:?} != crdt {real:?}"));
            }
            if cache != reference {
                return Err(format!("peer {p}: {cache:?} != peer 0 {reference:?}"));
            }
            if cache.is_none()
                && self.peers[p].dir.path().join(&self.name).exists() {
                    return Err(format!("peer {p}: file removed in crdt but on disk"));
                }
            if self.replace
                && let Some(Content::Bytes(bytes)) = &cache
                && self.peers[p].editors.iter().all(Option::is_none)
            {
                let disk = std::fs::read(self.peers[p].dir.path().join("a")).unwrap_or_default();
                if &disk != bytes {
                    return Err(format!("peer {p}: disk {disk:?} != crdt bytes {bytes:?}"));
                }
            }
            if let Some(Content::String(text)) = &cache {
                for e in 0..2 {
                    if let Some(ed) = &self.peers[p].editors[e]
                        && self.peers[p].actor.editor_connections[&(e + 1)].0.owns(&self.path)
                        && &ed.buffer != text
                    {
                        let ot = self.peers[p].actor.editor_connections[&(e + 1)]
                            .0
                            .debug_ot(&self.path);
                        return Err(format!("peer {p} editor {e}: editor {:?} != crdt {text:?}; rev_daemon {} rev_editor {} ot {ot}", ed.buffer, ed.rev_daemon, ed.rev_editor));
                    }
                }
                // The daemon only keeps the disk of files no editor owns in step.
                if !self.replace && self.peers[p].editors.iter().any(Option::is_some) {
                    continue;
                }
                // A file the user deleted under an open editor stays deleted while its text is empty.
                let disk = std::fs::read_to_string(self.peers[p].dir.path().join(&self.name))
                    .or_else(|e| if text.is_empty() { Ok(String::new()) } else { Err(e) })
                    .map_err(|e| format!("peer {p}: disk: {e}"))?;
                if &disk != text {
                    return Err(format!("peer {p}: disk {disk:?} != crdt {text:?}"));
                }
            }
        }
        Ok(())
    }
}

async fn run_seed(seed: u64, peers: usize, steps: usize, disk_writes: bool) -> Result<(), String> {
    run_seed_with(seed, peers, steps, disk_writes, false).await
}

async fn run_seed_with(seed: u64, peers: usize, steps: usize, disk_writes: bool, replace: bool) -> Result<(), String> {
    let mut w = World::new(seed, peers).await;
    w.disk_writes = disk_writes;
    w.replace = replace;
    for _ in 0..steps {
        w.step().await;
        if std::env::var("RACE_STEPCHECK").is_ok() {
            for p in 0..peers {
                let actor = &mut w.peers[p].actor;
                let cache = actor.current_file_content(&w.path).cloned();
                let real = Document::load(&actor.crdt_doc.save()).current_file_content(&w.path).cloned();
                if cache != real {
                    return Err(format!("step check: peer {p} cache {cache:?} crdt {real:?}\ntrace:\n{}", w.trace.join("\n")));
                }
            }
        }
    }
    w.quiesce().await;
    if let Some(v) = &w.violation {
        return Err(format!("seed {seed}: {v}\ntrace:\n{}", w.trace.join("\n")));
    }
    if w.unsettled {
        w.unsettled = false;
        w.verbose = true;
        for round in 0..6 {
            w.sync_all_rounds(1).await;
            for p in 0..peers {
                let c = w.peers[p].actor.current_file_content(&w.path).cloned();
                let d = std::fs::read_to_string(w.peers[p].dir.path().join(&w.name)).ok();
                let heads = w.peers[p].actor.crdt_doc.get_heads();
                let files = w.peers[p].actor.crdt_doc.files();
                w.trace.push(format!("round {round} peer {p}: crdt {c:?} disk {d:?} editor {} heads {heads:?} files {files:?}", w.peers[p].editors.iter().any(Option::is_some)));
            }
        }
        return Err(format!("seed {seed}: sync did not settle\ntrace:\n{}", w.trace.join("\n")));
    }
    w.check().map_err(|e| format!("seed {seed}: {e}\ntrace:\n{}", w.trace.join("\n")))
}

#[tokio::test]
async fn random_interleavings_converge_two_peers() {
    for seed in 0..seed_count(60) {
        if let Err(e) = run_seed(seed, 2, 60, true).await {
            panic!("{e}");
        }
    }
}

#[tokio::test]
async fn random_interleavings_converge_three_peers() {
    for seed in 0..seed_count(40) {
        if let Err(e) = run_seed(1000 + seed, 3, 80, true).await {
            panic!("{e}");
        }
    }
}

#[tokio::test]
async fn random_replacements_converge_two_peers() {
    for seed in 0..seed_count(150) {
        if let Err(e) = run_seed_with(5000 + seed, 2, 70, true, true).await {
            panic!("{e}");
        }
    }
}

#[tokio::test]
async fn random_replacements_converge_three_peers() {
    for seed in 0..seed_count(100) {
        if let Err(e) = run_seed_with(8000 + seed, 3, 90, true, true).await {
            panic!("{e}");
        }
    }
}

// Seeds that failed before the fixes: 8067 (a text object that lost a concurrent replacement
// becomes visible when the winner is deleted, with none of its text reported as patches, so
// the cache stayed empty) and 8189 (a deletion under an open editor lost against a peer's
// text and the surviving text was never written back to disk), 8789 (concurrent binary
// replacements: the cache took the losing value).
#[tokio::test]
async fn replacement_regression_seeds() {
    for seed in [8067, 8189, 8789] {
        if let Err(e) = run_seed_with(seed, 3, 90, true, true).await {
            panic!("{e}");
        }
    }
}

fn seed_count(default: u64) -> u64 {
    std::env::var("RACE_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

#[tokio::test]
#[tracing_test::traced_test]
async fn single_seed_debug() {
    let Some(seed) = std::env::var("RACE_SEED").ok().and_then(|s| s.parse().ok()) else {
        return;
    };
    let peers = std::env::var("RACE_PEERS").ok().and_then(|s| s.parse().ok()).unwrap_or(3);
    let steps = std::env::var("RACE_STEPS").ok().and_then(|s| s.parse().ok()).unwrap_or(80);
    if let Err(e) = run_seed(seed, peers, steps, true).await {
        panic!("{e}");
    }
}

// A peer removes its disk file because another peer deleted the file. When the file is created
// again later, the peer must write it instead of mistaking the stale disk record for a local
// deletion and deleting the new file from the shared document for everyone.
#[tokio::test]
async fn recreated_file_is_not_deleted_by_peer_that_removed_it() {
    let mut w = World::new(0, 2).await;
    let (a, b) = (w.peers[0].dir.path().join("a"), w.peers[1].dir.path().join("a"));
    assert_eq!(std::fs::read_to_string(&b).unwrap(), "one\ntwo\nthree\n");
    std::fs::remove_file(&a).unwrap();
    w.peers[0].watcher.push_back(WatcherEventType::Removed);
    w.watcher(0).await;
    w.sync_all().await;
    assert!(!b.exists(), "deletion reaches the other peer");
    std::fs::write(&a, "new\n").unwrap();
    w.peers[0].watcher.push_back(WatcherEventType::Created);
    w.watcher(0).await;
    w.sync_all().await;
    w.check().unwrap();
    assert_eq!(std::fs::read_to_string(&b).unwrap(), "new\n");
    assert_eq!(std::fs::read_to_string(&a).unwrap(), "new\n");
}

// An outside process can write the very text a peer's edit has just made shared, between the
// daemon's disk read and its comparison. The daemon then finds the bytes equal and does not write,
// but must still record them as the last bytes seen: with the old record, the watcher event for
// that write merged the text as a concurrent outside edit and duplicated it.
#[test]
fn found_equal_bytes_are_recorded_as_last_seen_on_disk() {
    let dir = tempdir().unwrap();
    std::fs::write(dir.path().join("a"), "ab").unwrap();
    let mut actor = peer_actor(&dir, true);
    let path = RelativePath::new("a");
    actor.disk_content.insert(path.clone(), b"a".to_vec());
    actor.crdt_doc.update_text("ab", &path);
    actor.ensure_file_has_bytes(&path, b"ab").unwrap();
    assert_eq!(actor.disk_content.get(&path), Some(&b"ab".to_vec()));
    actor.file_created_or_changed(&path);
    assert_eq!(
        actor.current_file_content(&path),
        Some(&Content::String("ab".into()))
    );
}

// The plugin protocol has no session id: an editor applies a daemon edit iff its revision equals
// the editor's own edit count. After close and reopen on one connection the count restarts at 0,
// so a daemon edit of the old session that is still in flight is applied to the new buffer.
// Editors must therefore take the daemon's answer to `close` (which follows every earlier daemon
// edit on the connection) before opening again, as the VS Code plugin does; the Emacs plugin
// ignores edits until its `open` is answered. Verus model: daemon_proof (`reopen_without_barrier`).
#[test]
fn reopened_session_applies_stale_daemon_edit_unless_old_messages_are_drained() {
    let mut old_server = crate::ot::OTServer::new("a".into());
    let mut delta = TextDelta::default();
    delta.insert("x");
    delta.retain(1);
    let stale = old_server.apply_crdt_change(&delta).unwrap();
    assert_eq!(stale.revision, 0);
    // The daemon writes "xa" to disk, the editor reopens it: a fresh session at revision 0.
    let new_server = crate::ot::OTServer::new("xa".into());
    let mut buffer = "xa".to_string();
    // Without a barrier the stale message (revision 0 == the new editor revision 0) is accepted.
    let accepted = stale.revision == 0;
    assert!(accepted);
    buffer = apply_editor_delta(&buffer, &stale.delta);
    assert_ne!(buffer, new_server.current_content(), "editor diverged: {buffer:?}");
    // With the barrier the stale message is read before the new session exists and dropped.
    assert_eq!(new_server.current_content(), "xa");
}

// Property behind the disk-coherence proof (daemon_proof/daemon_proof/disk_full.rs, `axiom_merge_clean`):
// when the shared text still equals the last bytes seen on disk, an outside change is merged to
// exactly the outside text, so shared text and disk agree again without a write.
#[test]
fn merging_an_outside_change_into_unchanged_shared_text_gives_the_outside_text() {
    let mut rng = StdRng::seed_from_u64(7);
    let alphabet = ["x", "y", "z", "\n", "é", "🥕", " "];
    let random = |rng: &mut StdRng| -> String {
        let n = rng.random_range(0..12);
        repeat_with(|| alphabet[rng.random_range(0..alphabet.len())])
            .take(n)
            .collect()
    };
    let dir = tempdir().unwrap();
    let mut actor = peer_actor(&dir, true);
    let path = RelativePath::new("m");
    for _ in 0..400 {
        let (base, outside) = (random(&mut rng), random(&mut rng));
        actor.crdt_doc.update_text(&base, &path);
        actor.disk_content.insert(path.clone(), base.clone().into_bytes());
        actor.merge_disk_content(&path, outside.clone().into_bytes());
        assert_eq!(
            actor.current_file_content(&path),
            Some(&Content::String(outside.clone())),
            "base {base:?} outside {outside:?}"
        );
    }
}

// File names with URI-reserved characters: the editor's `open` and `edit` must land in that very
// file, the shared document must key it by that name, and the other peer must write that file.
#[tokio::test]
async fn reserved_character_file_names_survive_editor_to_daemon_to_peer() {
    for name in ["a#b?c%20d e", "x?y", "100%", "back\\slash", "caf\u{e9} #1", "%2e%2e", "q#"] {
        let mut w = World::named(0, 2, name).await;
        let (a, b) = (w.peers[0].dir.path().join(name), w.peers[1].dir.path().join(name));
        assert_eq!(std::fs::read_to_string(&b).unwrap(), "one\ntwo\nthree\n", "{name}");
        w.open_editor(0, 0).await;
        w.local_edit(0, 0);
        w.send_to_daemon(0, 0).await;
        w.sync_all().await;
        let expected = w.peers[0].editors[0].as_ref().unwrap().buffer.clone();
        w.check().unwrap();
        assert_eq!(std::fs::read_to_string(&b).unwrap(), expected, "{name}");
        assert_eq!(std::fs::read_to_string(&a).unwrap(), expected, "{name}");
        for p in &w.peers {
            let listed: Vec<_> = std::fs::read_dir(p.dir.path())
                .unwrap()
                .filter_map(Result::ok)
                .filter(|e| e.file_name() != ".teamtypev")
                .collect();
            assert_eq!(listed.len(), 1, "{name}: stray files {listed:?}");
        }
    }
}

// An outside process creates a file that the daemon has never seen (no `disk_content` record)
// while a peer creates the same path. If the daemon writes the peer's text before the watcher
// event for the outside file arrives, the displaced outside bytes must still reach the shared
// document; the later watcher event only sees the daemon's own bytes.
#[test]
fn outside_created_file_displaced_before_its_watcher_event_is_merged() {
    for persist in [false, true] {
        let dir = tempdir().unwrap();
        let mut actor = peer_actor(&dir, true);
        actor.persist = persist;
        let path = RelativePath::new("n");
        actor.crdt_doc.update_text("peer\n", &path);
        std::fs::write(dir.path().join("n"), "local\n").unwrap();
        assert!(!actor.disk_content.contains_key(&path));
        actor.write_file(&path);
        actor.file_created_or_changed(&path);
        let shared = match actor.current_file_content(&path) {
            Some(Content::String(text)) => text.clone(),
            other => panic!("unexpected {other:?}"),
        };
        assert!(shared.contains("local"), "outside text lost: {shared:?}");
        assert!(shared.contains("peer"), "shared text replaced by the outside file: {shared:?}");
        assert_eq!(std::fs::read_to_string(dir.path().join("n")).unwrap(), shared);
    }
}

// A peer deletes a file while an outside process on this peer has rewritten it and the watcher
// event for that write is not yet handled. Applying the peer's delete removes the disk file
// without comparing it to `disk_content`, so the outside text is gone from disk and from every
// document; the late watcher event finds no file. (On restart the same race is resolved the other
// way: "Changed on disk while peers deleted it: the edit wins and is shared again.")
// Failed before the fix on branch tvd-review.
#[tokio::test]
async fn peer_delete_keeps_an_unhandled_outside_write() {
    let mut w = World::new(1, 2).await;
    let file1 = w.peers[1].dir.path().join("a");
    assert_eq!(std::fs::read_to_string(&file1).unwrap(), "one\ntwo\nthree\n");
    // Peer 0 deletes the file.
    std::fs::remove_file(w.peers[0].dir.path().join("a")).unwrap();
    let path = w.path.clone();
    w.peers[0].actor.file_created_or_changed(&path);
    // Peer 1: an outside write whose watcher event is still queued.
    std::fs::write(&file1, "one\ntwo\nthree\nunsaved work\n").unwrap();
    w.sync_all().await;
    w.peers[1].actor.file_created_or_changed(&path);
    w.sync_all().await;
    let on_disk = std::fs::read_to_string(&file1).ok();
    let shared = w.peers[1].actor.current_file_content(&path).cloned();
    assert!(
        on_disk.as_deref().is_some_and(|t| t.contains("unsaved work"))
            || matches!(&shared, Some(Content::String(t)) if t.contains("unsaved work")),
        "outside write lost: disk {on_disk:?}, shared {shared:?}"
    );
}

// Same race while a Git command runs: the peer's delete is deferred, and an outside write to the
// file during the command is not yet read. `finish_git` applied deferred removals before its
// rescan and without comparing to `disk_content`, so the outside text was lost.
// Failed before the fix on branch tvd-git-removal.
#[tokio::test]
async fn deferred_git_removal_keeps_an_outside_write() {
    let mut w = World::new(1, 2).await;
    let file1 = w.peers[1].dir.path().join("a");
    assert_eq!(std::fs::read_to_string(&file1).unwrap(), "one\ntwo\nthree\n");
    w.peers[1].actor.git_running = true;
    std::fs::remove_file(w.peers[0].dir.path().join("a")).unwrap();
    let path = w.path.clone();
    w.peers[0].actor.file_created_or_changed(&path);
    w.sync_all().await;
    assert!(file1.exists(), "removal must be deferred while Git runs");
    // Outside write (e.g. by the Git command) while Git runs.
    std::fs::write(&file1, "one\ntwo\nthree\nunsaved work\n").unwrap();
    w.peers[1].actor.finish_git().unwrap();
    w.peers[1].actor.file_created_or_changed(&path);
    w.sync_all().await;
    let on_disk = std::fs::read_to_string(&file1).ok();
    let shared = w.peers[1].actor.current_file_content(&path).cloned();
    assert!(
        on_disk.as_deref().is_some_and(|t| t.contains("unsaved work"))
            || matches!(&shared, Some(Content::String(t)) if t.contains("unsaved work")),
        "outside write lost: disk {on_disk:?}, shared {shared:?}"
    );
}
