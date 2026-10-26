// SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::{collections::HashMap, mem};

use anyhow::{Context, Result, bail};
use async_trait::async_trait;
use automerge::sync::{Message as AutomergeSyncMessage, State as AutomergeSyncState};
use serde::{Deserialize, Serialize};
use tokio::sync::{broadcast::error::RecvError, oneshot};
use tracing::{debug, error};

use crate::daemon::{DocMessage, DocumentActorHandle};
use crate::git_forward::{Request, Response};
use crate::types::EphemeralMessage;

#[derive(Deserialize, Serialize)]
/// The `PeerMessage` is used for peer to peer data exchange.
pub enum PeerMessage {
    /// The Sync message contains the changes to the CRDT
    Sync(Vec<u8>),
    /// The Ephemeral message currently is used for cursor messages, but can later be used for
    /// other things that should not be persisted.
    Ephemeral(EphemeralMessage),
    GitRequest(Request),
    GitInput(u64, Vec<u8>),
    GitInputAck(u64),
    GitResponse(u64, Response),
    GitCancel(u64),
    GitAck(u64),
    /// Sent first: the sender's history ID, or an empty string.
    Hello(String),
    /// Keeps the ordered sync stream active so stalled reads cause a reconnect.
    Heartbeat,
}

#[async_trait]
pub trait Connection<T>: Send + Sync {
    async fn send(&mut self, message: T) -> Result<()>;
    async fn next(&mut self) -> Result<T>;
}

/// Transport-agnostic logic of how to sync with another peer.
/// Exchanges [`PeerMessage`]s with the connection, and communicates with the document on the other side.
/// Maintains the sync state.
pub struct SyncActor {
    peer_state: AutomergeSyncState,
    document_handle: DocumentActorHandle,
    connection: Box<dyn Connection<PeerMessage>>,
    pending_git: HashMap<u64, tokio::sync::mpsc::Sender<Response>>,
    running_git: HashMap<u64, oneshot::Sender<()>>,
    git_output: tokio::sync::mpsc::Sender<(u64, Response)>,
    git_output_rx: tokio::sync::mpsc::Receiver<(u64, Response)>,
    git_credits: HashMap<u64, std::sync::Arc<tokio::sync::Semaphore>>,
    git_ack: tokio::sync::mpsc::Sender<u64>,
    git_ack_rx: tokio::sync::mpsc::Receiver<u64>,
    git_inputs: HashMap<u64, crate::git_forward::InputWriter>,
    git_input_tx: tokio::sync::mpsc::Sender<PeerMessage>,
    git_input_rx: tokio::sync::mpsc::Receiver<PeerMessage>,
    git_input_acks: HashMap<u64, tokio::sync::mpsc::Sender<()>>,
    git_uploads: HashMap<u64, tokio::task::AbortHandle>,
    git_tasks: tokio::task::JoinSet<()>,
}

impl SyncActor {
    pub fn new(
        document_handle: DocumentActorHandle,
        connection: Box<dyn Connection<PeerMessage>>,
    ) -> Self {
        let (git_output, git_output_rx) = tokio::sync::mpsc::channel(8);
        let (git_ack, git_ack_rx) = tokio::sync::mpsc::channel(8);
        let (git_input_tx, git_input_rx) = tokio::sync::mpsc::channel(1);
        Self {
            git_inputs: HashMap::new(),
            git_input_tx,
            git_input_rx,
            git_input_acks: HashMap::new(),
            git_uploads: HashMap::new(),
            git_tasks: tokio::task::JoinSet::new(),
            git_credits: HashMap::new(),
            git_ack,
            git_ack_rx,
            pending_git: HashMap::new(),
            running_git: HashMap::new(),
            git_output,
            git_output_rx,
            peer_state: AutomergeSyncState::new(),
            document_handle,
            connection,
        }
    }

    async fn receive_peer_message(&mut self, message: PeerMessage) -> Result<()> {
        let (response_tx, response_rx) = oneshot::channel();
        match message {
            PeerMessage::Sync(message_buf) => {
                let message = AutomergeSyncMessage::decode(&message_buf)?;
                self.document_handle
                    .send_message(DocMessage::ReceiveSyncMessage {
                        message,
                        state: mem::take(&mut self.peer_state),
                        response_tx,
                    })
                    .await;
                self.peer_state = response_rx
                    .await
                    .expect("Couldn't read response from Document channel");
            }
            PeerMessage::Ephemeral(cursor) => {
                self.document_handle
                    .send_message(DocMessage::ReceiveEphemeral(cursor))
                    .await;
            }
            PeerMessage::Hello(theirs) => self.check_history(&theirs).await,
            PeerMessage::Heartbeat => {}
            PeerMessage::GitRequest(request) => {
                if !self.document_handle.is_host() {
                    bail!("Only the sharer accepts Git requests");
                }
                self.connection
                    .send(PeerMessage::GitResponse(request.id, Response::Accepted))
                    .await?;
                let id = request.id;
                let (input, writer) = crate::git_forward::Input::new()?;
                self.git_inputs.insert(id, writer);
                let (response, mut responses) = tokio::sync::mpsc::channel(8);
                let git = self.document_handle.git.clone();
                let output = self.git_output.clone();
                let (cancel, mut cancelled) = oneshot::channel();
                self.running_git.insert(id, cancel);
                let credit = std::sync::Arc::new(tokio::sync::Semaphore::new(1));
                self.git_credits.insert(id, credit.clone());
                self.git_tasks.spawn(async move {
                    let queued = tokio::select! {
                        result = git.enqueue(crate::git_forward::Job { request, response, input }) => result.is_ok(),
                        _ = &mut cancelled => return,
                    };
                    if !queued {
                        let _ = output
                            .send((id, Response::Error("Git worker stopped".into())))
                            .await;
                        return;
                    }
                    loop {
                        tokio::select! {
                            response = responses.recv() => {
                                let Some(response) = response else { break; };
                                let finished = response.finished();
                                let sent = tokio::select! {
                                    result = async {
                                        let Ok(Ok(permit)) = tokio::time::timeout(crate::git_forward::OUTPUT_TIMEOUT, credit.acquire()).await else { return false; };
                                        permit.forget();
                                        output.send((id, response)).await.is_ok()
                                    } => result,
                                    _ = &mut cancelled => false,
                                };
                                if !sent || finished { break; }
                            }
                            () = output.closed() => break,
                            _ = &mut cancelled => break,
                        }
                    }
                });
            }
            PeerMessage::GitInput(id, bytes) => {
                if let Some(input) = self.git_inputs.get_mut(&id) {
                    input.write(&bytes)?;
                    if bytes.is_empty() {
                        self.git_inputs.remove(&id);
                    } else {
                        self.connection.send(PeerMessage::GitInputAck(id)).await?;
                    }
                }
            }
            PeerMessage::GitResponse(id, response) => {
                if self.document_handle.is_host() {
                    bail!("Unexpected Git response on the sharer");
                }
                let finished = response.finished();
                let acknowledge = !matches!(response, Response::Accepted);
                if let Some(sender) = self.pending_git.get(&id).cloned() {
                    let ack = self.git_ack.clone();
                    self.git_tasks.spawn(async move {
                        if sender.send(response).await.is_ok() && acknowledge {
                            let _ = ack.send(id).await;
                        }
                    });
                } else {
                    self.connection.send(PeerMessage::GitCancel(id)).await?;
                }
                if finished {
                    self.pending_git.remove(&id);
                    self.git_input_acks.remove(&id);
                    if let Some(upload) = self.git_uploads.remove(&id) {
                        upload.abort();
                    }
                }
            }
            PeerMessage::GitInputAck(id) => {
                if let Some(ack) = self.git_input_acks.get(&id) {
                    let _ = ack.try_send(());
                }
            }
            PeerMessage::GitCancel(id) => {
                self.git_inputs.remove(&id);
                self.git_input_acks.remove(&id);
                self.git_credits.remove(&id);
                if let Some(cancel) = self.running_git.remove(&id) {
                    let _ = cancel.send(());
                }
            }
            PeerMessage::GitAck(id) => {
                if let Some(credit) = self.git_credits.get(&id) {
                    credit.add_permits(1);
                }
            }
        }
        Ok(())
    }

    // 🧑 "Prevent this bug in the future. Should likely prioritize server history"
    /// At a joiner: refuses to merge a history other than the sharer's. Merging two histories
    /// replaces each file both have with one side's version wholesale, which once reverted the
    /// sharer's files to a joiner's stale copies. The sharer's history wins: the joiner drops its
    /// own and stops, and joining again takes the sharer's files.
    async fn check_history(&self, theirs: &str) {
        if self.document_handle.is_host() || theirs.is_empty() {
            return;
        }
        let (mine, has_files) = self.document_handle.history_id().await;
        if mine.as_deref() == Some(theirs) || (mine.is_none() && !has_files) {
            return;
        }
        error!(
            "The sharer started a new history, so your changes here cannot be merged with theirs. Nothing was overwritten. Save any changes you made since you were last connected elsewhere, then run `teamtypev join` again; it asks before replacing this directory's files with the sharer's."
        );
        let teamtypev_dir = self.document_handle.base_dir().join(".teamtypev");
        let _ = std::fs::remove_file(teamtypev_dir.join("doc"));
        // So that the next join asks before overwriting.
        let _ = std::fs::remove_file(teamtypev_dir.join("joined"));
        std::process::exit(1);
    }

    async fn generate_sync_message(&mut self) -> Result<()> {
        let (response_tx, response_rx) = oneshot::channel();
        self.document_handle
            .send_message(DocMessage::GenerateSyncMessage {
                state: mem::take(&mut self.peer_state),
                response_tx,
            })
            .await;
        let (ps, message) = response_rx
            .await
            .context("Could not read response from Document channel")?;
        self.peer_state = ps;
        if let Some(message) = message {
            self.connection
                .send(PeerMessage::Sync(message.encode()))
                .await?;
        }
        Ok(())
    }

    // Convention: If this method returns an Ok, the connection timed out.
    // On other errors, it returns an Err.
    pub async fn run(mut self) -> Result<()> {
        let mut doc_changed_ping_rx = self.document_handle.subscribe_document_changes();
        let mut ephemeral_messages_rx = self.document_handle.subscribe_ephemeral_messages();
        let mut git_requests = self.document_handle.git.outgoing.subscribe();

        let (history, _) = self.document_handle.history_id().await;
        self.connection
            .send(PeerMessage::Hello(history.unwrap_or_default()))
            .await?;

        // Kick off initial synchronization with peer.
        self.generate_sync_message().await?;

        let mut git_cleanup = tokio::time::interval(std::time::Duration::from_millis(50));
        loop {
            tokio::select! {
                _ = self.git_tasks.join_next(), if !self.git_tasks.is_empty() => {}
                _ = git_cleanup.tick() => {
                    let closed: Vec<_> = self.pending_git.iter().filter(|(_, sender)| sender.is_closed()).map(|(&id, _)| id).collect();
                    for id in closed {
                        self.pending_git.remove(&id);
                        self.git_input_acks.remove(&id);
                        if let Some(upload) = self.git_uploads.remove(&id) {
                            upload.abort();
                        }
                        self.connection.send(PeerMessage::GitCancel(id)).await?;
                    }
                    self.running_git.retain(|_, cancel| !cancel.is_closed());
                    self.git_inputs.retain(|id, _| self.running_git.contains_key(id));
                    self.git_credits.retain(|id, _| self.running_git.contains_key(id));
                    self.git_input_acks.retain(|_, ack| !ack.is_closed());
                }
                // As doc_changed_ping_rx is a broadcast channel our understanding is,
                // that this breaks a potential cyclic deadlock between SyncerActor
                // and TCPActor (e.g. when TCPWriteActor.send blocks).
                doc_ping = doc_changed_ping_rx.recv() => {
                    match doc_ping {
                        Ok(()) => { self.generate_sync_message().await?; }
                        Err(RecvError::Closed) => {
                            panic!("Doc changed channel has been closed");
                        }
                        Err(RecvError::Lagged(_)) => {
                            // This is fine, the messages in this channel are just pings.
                            // It's fine if we miss some.
                            debug!("Doc changed ping channel lagged (this is probably fine).");
                        }
                    }
                }
                ephemeral_message = ephemeral_messages_rx.recv() => {
                    match ephemeral_message {
                        Ok(ephemeral_message) => {
                            self.connection.send(PeerMessage::Ephemeral(ephemeral_message)).await?;
                        }
                        Err(RecvError::Closed) => {
                            panic!("Ephemeral message channel has been closed");
                        }
                        Err(RecvError::Lagged(_)) => {
                            // We missed some cursor states, because of the limited
                            // capacity of the channel.
                            debug!("Ephemeral message channel lagged (this is unfortunate, but okay).");
                        }
                    }
                }
                request = git_requests.recv(), if !self.document_handle.is_host() => {
                    let job = request.context("Git request channel lagged; reconnect")?;
                    self.pending_git.insert(job.request.id, job.response.clone());
                    self.generate_sync_message().await?;
                    let sender = self.git_input_tx.clone();
                    let (ack, mut acknowledgements) = tokio::sync::mpsc::channel(1);
                    self.git_input_acks.insert(job.request.id, ack);
                    let id = job.request.id;
                    let upload = self.git_tasks.spawn(async move {
                        let id = job.request.id;
                        let result: Result<()> = async {
                            sender.send(PeerMessage::GitRequest(job.request)).await?;
                            let mut input = job.input.reader().await?;
                            let mut bytes = vec![0; crate::git_forward::INPUT_CHUNK];
                            loop {
                                let count = input.read(&mut bytes).await?;
                                sender.send(PeerMessage::GitInput(id, bytes[..count].to_vec())).await?;
                                if count == 0 { return Ok(()); }
                                acknowledgements.recv().await.context("Git stdin upload cancelled")?;
                            }
                        }.await;
                        if let Err(error) = result {
                            let _ = job.response.send(Response::Error(format!("Could not forward Git stdin: {error:#}"))).await;
                            let _ = sender.send(PeerMessage::GitCancel(id)).await;
                        }
                    });
                    self.git_uploads.insert(id, upload);
                }
                Some(input) = self.git_input_rx.recv() => {
                    self.connection.send(input).await?;
                }
                Some((id, response)) = self.git_output_rx.recv() => {
                    self.connection.send(PeerMessage::GitResponse(id, response)).await?;
                }
                Some(id) = self.git_ack_rx.recv() => {
                    self.connection.send(PeerMessage::GitAck(id)).await?;
                }
                message = self.connection.next() => {
                    self.receive_peer_message(message?).await?;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::AppConfig;
    use crate::document::{Content, Document};
    use crate::path::RelativePath;
    use std::process::Command;

    struct UnusedConnection;

    #[async_trait]
    impl Connection<PeerMessage> for UnusedConnection {
        async fn send(&mut self, _: PeerMessage) -> Result<()> {
            unreachable!("History checks do not use the transport")
        }

        async fn next(&mut self) -> Result<PeerMessage> {
            unreachable!("History checks do not use the transport")
        }
    }

    fn fixture(base_dir: &std::path::Path, history: Option<&str>, has_files: bool) -> Result<()> {
        std::fs::create_dir(base_dir.join(".teamtypev"))?;
        let mut document = Document::default();
        if let Some(history) = history {
            let mut bytes = vec![0xff];
            bytes.extend_from_slice(history.as_bytes());
            document.set_file(
                Content::Bytes(bytes),
                &RelativePath::new(".teamtype/history"),
            );
        }
        if has_files {
            document.set_file(
                Content::String("local changes".into()),
                &RelativePath::new("local.txt"),
            );
            std::fs::write(base_dir.join("local.txt"), "local changes")?;
        }
        std::fs::write(base_dir.join(".teamtypev/doc"), document.save())?;
        std::fs::write(base_dir.join(".teamtypev/joined"), "joined")?;
        Ok(())
    }

    fn actor(base_dir: &std::path::Path, is_host: bool) -> SyncActor {
        let config = AppConfig {
            base_dir: base_dir.into(),
            ..AppConfig::default()
        };
        SyncActor::new(
            DocumentActorHandle::new(&config, false, is_host, true),
            Box::new(UnusedConnection),
        )
    }

    #[tokio::test]
    async fn compatible_history_and_hosts_keep_local_state() -> Result<()> {
        for (is_host, history, has_files, remote) in [
            (false, Some("same"), true, "same"),
            (false, None, false, "new"),
            (false, Some("old"), true, ""),
            (true, Some("old"), true, "new"),
        ] {
            let directory = tempfile::tempdir()?;
            fixture(directory.path(), history, has_files)?;
            let mut syncer = actor(directory.path(), is_host);
            let before = syncer.document_handle.history_id().await;
            syncer.receive_peer_message(PeerMessage::Heartbeat).await?;
            syncer.check_history(remote).await;
            assert_eq!(syncer.document_handle.history_id().await, before);
            assert!(directory.path().join(".teamtypev/doc").exists());
            assert!(directory.path().join(".teamtypev/joined").exists());
        }
        Ok(())
    }

    #[test]
    fn incompatible_history_refuses_without_overwriting_local_files() -> Result<()> {
        for history in [Some("old"), None] {
            let directory = tempfile::tempdir()?;
            fixture(directory.path(), history, true)?;
            let output = Command::new(std::env::current_exe()?)
                .args([
                    "--exact",
                    "peer::sync::tests::history_refusal_child",
                    "--nocapture",
                ])
                .env("TEAMTYPEV_HISTORY_REFUSAL_TEST_DIR", directory.path())
                .output()?;
            assert_eq!(
                output.status.code(),
                Some(1),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(!directory.path().join(".teamtypev/doc").exists());
            assert!(!directory.path().join(".teamtypev/joined").exists());
            assert_eq!(
                std::fs::read_to_string(directory.path().join("local.txt"))?,
                "local changes"
            );
        }
        Ok(())
    }

    #[tokio::test]
    async fn history_refusal_child() -> Result<()> {
        let Some(directory) = std::env::var_os("TEAMTYPEV_HISTORY_REFUSAL_TEST_DIR") else {
            return Ok(());
        };
        actor(std::path::Path::new(&directory), false)
            .check_history("new")
            .await;
        anyhow::bail!("History mismatch did not terminate the joiner")
    }
}
