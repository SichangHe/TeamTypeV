// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::iter::repeat_with;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use anyhow::Result;
use automerge::ChangeHash;
use automerge::{
    Patch,
    sync::{Message as AutomergeSyncMessage, State as SyncState},
};
use docstr::docstr;
use futures::SinkExt;
use rand::RngExt;
use tokio::sync::broadcast::error::RecvError;
use tokio::{
    sync::{broadcast, mpsc, oneshot},
    time::sleep,
    time::{Duration, Instant},
};
use tracing::{debug, error, info, warn};

use crate::config::{self, AppConfig};
use crate::document::{self, Document};
use crate::editor::{self, EditorId, EditorWriter};
use crate::editor_connection::EditorConnection;
use crate::editor_protocol::{
    EditorProtocolMessageError, EditorProtocolMessageFromEditor, EditorProtocolMessageToEditor,
    IncomingMessage, JSONRPCResponse, OutgoingMessage,
};
use crate::path::{AbsolutePath, RelativePath};
use crate::peer;
use crate::sandbox;
use crate::types::{
    ComponentMessage, CursorId, CursorState, EphemeralMessage, FileTextDelta, PatchEffect,
    TextDelta,
};
use crate::vcs_files::{self, VcsMessage};
use crate::vcs_lock::{self, GitLock, Holder};
use crate::watcher::WatcherEvent;
use crate::watcher::{Watcher, WatcherEventType};
use crate::wormhole::put_secret_address_into_wormhole;

// 🧑 "make it work for three or more people reliably"
/// One failed address lookup must not end a join: a live three-daemon trial lost a joiner that way.
const INITIAL_CONNECT_ATTEMPTS: usize = 5;
/// Identifies the sharer's history; set when the sharer starts a new one.
const HISTORY_ID: &str = ".teamtype/history";
const INITIAL_CONNECT_RETRY_DELAY: Duration = Duration::from_secs(2);

pub const TEST_FILE_PATH: &str = "text";

// These messages are sent to the task that owns the document.
#[must_use]
pub enum DocMessage {
    GetContent {
        response_tx: oneshot::Sender<Option<document::Content>>,
    },
    FromEditor(EditorId, IncomingMessage),
    ToEditor(EditorId, OutgoingMessage),
    FromWatcher(WatcherEvent),
    RescanFiles,
    CheckVcsLock,
    /// This document's history ID, and whether it has any files.
    HistoryId {
        response_tx: oneshot::Sender<(Option<String>, bool)>,
    },
    ReceiveVcs(VcsMessage),
    VcsSnapshot {
        response_tx: oneshot::Sender<Vec<VcsMessage>>,
    },
    Persist,
    RandomEdit,
    ReceiveSyncMessage {
        message: AutomergeSyncMessage,
        state: SyncState,
        response_tx: oneshot::Sender<SyncState>,
    },
    GenerateSyncMessage {
        state: SyncState,
        response_tx: oneshot::Sender<(SyncState, Option<AutomergeSyncMessage>)>,
    },
    NewEditorConnection(EditorId, EditorWriter),
    CloseEditorConnection(EditorId),
    ReceiveEphemeral(EphemeralMessage),
}

impl fmt::Debug for DocMessage {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let repr = match self {
            Self::GetContent { .. } => "GetContent".to_string(),
            Self::FromEditor(id, m) => format!("FromEditor({id}, {m:?})"),
            Self::ToEditor(id, m) => format!("ToEditor({id}, {m:?})"),
            Self::FromWatcher(e) => format!("FromWatcher({e:?}"),
            Self::RescanFiles => "RescanFiles".to_string(),
            Self::CheckVcsLock => "CheckVcsLock".to_string(),
            Self::HistoryId { .. } => "HistoryId".to_string(),
            Self::ReceiveVcs(_) => "ReceiveVcs".to_string(),
            Self::VcsSnapshot { .. } => "VcsSnapshot".to_string(),
            Self::Persist => "Persist".to_string(),
            Self::RandomEdit => "RandomEdit".to_string(),
            Self::ReceiveSyncMessage { .. } => "ReceiveSyncMessage".to_string(),
            Self::GenerateSyncMessage { .. } => "GenerateSyncMessage".to_string(),
            Self::NewEditorConnection(id, _) => format!("NewEditorConnection({id})"),
            Self::CloseEditorConnection(id) => format!("CloseEditorConnection({id})"),
            Self::ReceiveEphemeral(m) => format!("ReceiveEphemeral({m:?})"),
        };
        write!(f, "{repr}")
    }
}

type DocMessageSender = mpsc::Sender<DocMessage>;
type DocChangedSender = broadcast::Sender<()>;
type DocChangedReceiver = broadcast::Receiver<()>;
type EphemeralMessageSender = broadcast::Sender<EphemeralMessage>;
type EphemeralMessageReceiver = broadcast::Receiver<EphemeralMessage>;

/// This Actor is responsible for applying changes to the document asynchronously.
///
/// Any `DocMessage` that is emitted via `DocumentActorHandle` should have an effect eventually.
#[must_use]
pub struct DocumentActor {
    doc_message_rx: mpsc::Receiver<DocMessage>,
    doc_changed_ping_tx: DocChangedSender,
    ephemeral_message_tx: EphemeralMessageSender,
    editor_connections: HashMap<EditorId, (EditorConnection, EditorWriter)>,
    ephemeral_states: HashMap<CursorId, EphemeralMessage>,
    /// The Document is the main I/O managed resource of this actor.
    crdt_doc: Document,
    app_config: AppConfig,
    save_fully: bool,
    persist: bool,
    /// Files an editor has open. Kept on disk too: after a crash, files an editor saved itself may
    /// be ahead of the saved document on disk.
    files_open_in_editors: HashSet<RelativePath>,
    git_lock: GitLock,
    /// The last `teamtype git-lock` request we handled, and our announcement for it.
    git_lock_request: Option<(std::time::SystemTime, u64)>,
    /// Version-control file changes for the peers; see `vcs_files`.
    vcs_tx: broadcast::Sender<VcsMessage>,
    /// Hashes of the version-control files as last shared, to tell local changes apart.
    vcs_known: HashMap<RelativePath, u64>,
    /// Paths of the snapshot being received.
    vcs_snapshot_paths: HashSet<RelativePath>,
    /// Whether we have the sharer's version-control files, so that ours may be sent.
    vcs_ready: bool,
}

impl DocumentActor {
    fn new(
        doc_message_rx: mpsc::Receiver<DocMessage>,
        doc_changed_ping_tx: DocChangedSender,
        ephemeral_message_tx: EphemeralMessageSender,
        app_config: AppConfig,
        init: bool,
        is_host: bool,
        persist: bool,
    ) -> Self {
        // If there is a persisted version in base_dir/.teamtype/doc, load it.
        // TODO: Pull out ".teamtype" string into a constant.
        let persistence_file = app_config.base_dir.join(".teamtype/doc");
        let persistence_file_exists = sandbox::exists(&app_config.base_dir, &persistence_file)
            .expect("Could not check for the existence of the persistence file");

        let load_crdt_doc = persistence_file_exists && !init && persist;
        let crdt_doc = if load_crdt_doc {
            debug!(
                "Loading persisted CRDT document from '{}'.",
                persistence_file.display()
            );
            let bytes = sandbox::read_file(&app_config.base_dir, &persistence_file)
                .unwrap_or_else(|_| panic!("Could not read file '{}'", persistence_file.display()));
            Document::load(&bytes)
        } else {
            Document::default()
        };
        debug!("Loading CRDT document completed.");

        let mut s = Self {
            doc_message_rx,
            doc_changed_ping_tx,
            ephemeral_message_tx,
            editor_connections: HashMap::default(),
            ephemeral_states: HashMap::default(),
            app_config,
            crdt_doc,
            save_fully: true,
            persist,
            files_open_in_editors: HashSet::default(),
            git_lock: GitLock::new(String::new(), String::new(), is_host, vcs_lock::timeout()),
            git_lock_request: None,
            vcs_tx: broadcast::channel(100).0,
            vcs_known: HashMap::default(),
            vcs_snapshot_paths: HashSet::default(),
            vcs_ready: is_host,
        };
        s.git_lock = GitLock::new(
            s.load_peer_id(),
            s.app_config.username.clone().unwrap_or_default(),
            is_host,
            vcs_lock::timeout(),
        );
        s.install_git_hook();
        if is_host
            && s.current_file_content(&RelativePath::new(HISTORY_ID))
                .is_none()
        {
            // Starts with a byte that is invalid UTF-8, so that it is stored as bytes.
            let mut id = vec![0xFF];
            id.extend(
                repeat_with(|| format!("{:02x}", rand::rng().random::<u8>()))
                    .take(16)
                    .collect::<String>()
                    .bytes(),
            );
            s.crdt_doc
                .set_file(document::Content::Bytes(id), &RelativePath::new(HISTORY_ID));
        }

        if persistence_file_exists && persist {
            if !init {
                s.restore_files_left_open();
            }
            s.read_current_content_from_dir(init);
        } else if is_host {
            s.read_current_content_from_dir(true);
        }

        s
    }

    #[must_use]
    fn editor_saves(&self, file_path: &RelativePath) -> bool {
        self.editor_connections
            .values()
            .any(|connection| connection.0.saves(file_path))
    }

    /// If any editor owns the file, it means that the daemon doesn't have ownership.
    #[must_use]
    fn owns(&self, file_path: &RelativePath) -> bool {
        !self
            .editor_connections
            .values()
            .any(|connection| connection.0.owns(file_path))
    }

    async fn handle_message(&mut self, message: DocMessage) {
        debug!("Handling doc message: {message:?}");
        match message {
            DocMessage::GetContent { response_tx } => {
                response_tx
                    .send(
                        self.current_file_content(&RelativePath::new(TEST_FILE_PATH))
                            .cloned(),
                    )
                    .expect("Failed to send content to response channel");
            }
            DocMessage::RandomEdit => {
                let delta = self.random_delta();
                let message = ComponentMessage::Edit {
                    file_path: RelativePath::new(TEST_FILE_PATH),
                    delta,
                };
                self.process_component_message(None, &message).await;
            }
            DocMessage::FromEditor(editor_id, message) => {
                self.handle_message_from_editor(editor_id, message).await;
            }
            DocMessage::ToEditor(editor_id, message) => {
                self.send_to_editor_client(&editor_id, message).await;
            }
            DocMessage::FromWatcher(watcher_event) => {
                self.handle_watcher_event(&watcher_event);
            }
            DocMessage::RescanFiles => {
                self.read_current_content_from_dir(false);
            }
            DocMessage::CheckVcsLock => self.tick_git_lock(),
            DocMessage::HistoryId { response_tx } => {
                let id = match self.current_file_content(&RelativePath::new(HISTORY_ID)) {
                    Some(document::Content::Bytes(bytes)) => {
                        Some(String::from_utf8_lossy(&bytes[1..]).into_owned())
                    }
                    _ => None,
                };
                let has_files = self
                    .crdt_doc
                    .files()
                    .iter()
                    .any(|path| !vcs_lock::is_internal(path));
                let _ = response_tx.send((id, has_files));
            }
            DocMessage::ReceiveVcs(message) => self.receive_vcs(message),
            DocMessage::VcsSnapshot { response_tx } => {
                let _ = response_tx.send(vcs_files::snapshot_messages(self.local_vcs_files()));
            }
            DocMessage::Persist => self.persist(),
            DocMessage::ReceiveSyncMessage {
                message,
                state: mut peer_state,
                response_tx,
            } => {
                let heads_before_sync_message = self.get_heads();

                let patches = self.apply_sync_message_to_doc(message, &mut peer_state);

                let patch_effects = PatchEffect::from_crdt_patches(&patches);

                let mut file_deltas = vec![];

                for patch_effect in patch_effects {
                    match patch_effect {
                        PatchEffect::FileChange(file_text_delta) => {
                            file_deltas.push(file_text_delta);
                        }
                        PatchEffect::FileRemoval(file_path) => {
                            if vcs_lock::is_internal(&file_path) {
                                continue;
                            }
                            if self.owns(&file_path) && self.crdt_doc.file_exists(&file_path) {
                                // A peer's file of the same name replaced ours; no further
                                // patch arrives for it if it is empty.
                                self.write_file(&file_path);
                            } else if self.owns(&file_path) {
                                info!("Removing file {file_path}.");

                                sandbox::remove_file(
                                    &self.app_config.base_dir,
                                    &self.absolute_path_for_file_path(&file_path),
                                )
                                .unwrap_or_else(|err| {
                                    warn!("Failed to remove file {file_path}: {err}");
                                });
                            } else {
                                // At least one editor has the file open. We want to allow it to
                                // keep editing it. Conceptually, we want to treat the file as
                                // still there, but send deltas to the editor to make it empty.

                                // Delete all previous file_deltas touching that file. After the
                                // deletion, they are now irrelevant to the editor. And it's easier
                                // for us to find out the file's content directly before the sync
                                // message was applied.
                                file_deltas.retain(|d| d.file_path != file_path);

                                let content_before_sync_message = self
                                    .file_content_at(&file_path, &heads_before_sync_message)
                                    .expect("Could not get file content at heads");

                                // Create a delta that deletes all the previous content.
                                let mut text_delta = TextDelta::default();
                                text_delta.delete(content_before_sync_message.chars().count());
                                let delta = FileTextDelta {
                                    file_path: file_path.clone(),
                                    delta: text_delta,
                                };
                                file_deltas.push(delta);

                                // If the file doesn't exist anymore after the sync message was
                                // applied (which is now!), we'd like it to be there again. So
                                // re-create an empty version.
                                if self.crdt_doc.file_exists(&file_path) {
                                    // If the file is still there, the upcoming patches of the sync
                                    // message will re-add it for us. In that case, we don't want
                                    // to touch it in the doc, because we will send the
                                    // modifications to the editors, and these contents should be
                                    // consistent. So we don't need to do anything.
                                } else {
                                    info!(
                                        "Peer deleted {file_path}, but you have it open in an editor. Bringing back an empty version."
                                    );
                                    self.crdt_doc.update_text("", &file_path);
                                }
                            }
                        }
                        PatchEffect::FileBytes(file_path, bytes) => {
                            self.ensure_file_has_bytes(&file_path, &bytes);
                        }
                        PatchEffect::NoEffect => {}
                    }
                }

                self.write_files_changed_in_file_deltas(&file_deltas);
                self.tick_git_lock();

                for file_text_delta in &file_deltas {
                    let message = ComponentMessage::Edit {
                        file_path: file_text_delta.file_path.clone(),
                        delta: file_text_delta.delta.clone(),
                    };
                    self.broadcast_to_editors(None, &message).await;
                }

                if response_tx.send(peer_state).is_err() {
                    warn!("Failed to send peer state in response to ReceiveSyncMessage.");
                }
            }
            DocMessage::GenerateSyncMessage {
                state: mut peer_state,
                response_tx,
            } => {
                let message = self.crdt_doc.generate_sync_message(&mut peer_state);

                if response_tx.send((peer_state, message)).is_err() {
                    warn!(
                        "Failed to send peer state and sync message in response to GenerateSyncMessage."
                    );
                }
            }
            DocMessage::NewEditorConnection(id, editor_writer) => {
                let editor_connection_id = self.cursor_id(id);
                self.editor_connections.insert(
                    id,
                    (
                        EditorConnection::new(editor_connection_id, self.app_config.clone()),
                        editor_writer,
                    ),
                );

                // Send all known cursor states to editor.
                for (cursor_id, ephemeral_message) in self.ephemeral_states.clone() {
                    let message = ComponentMessage::Cursor {
                        cursor_id: cursor_id.clone(),
                        cursor_state: ephemeral_message.cursor_state.clone(),
                    };
                    self.send_to_editor(id, &message).await;
                }
            }
            DocMessage::CloseEditorConnection(editor_id) => {
                self.editor_connections.remove(&editor_id);
                self.release_files();

                let cursor_id = self.cursor_id(editor_id);
                debug!("Deleting cursor {cursor_id}.");
                self.maybe_delete_cursor_position(&cursor_id).await;
            }
            DocMessage::ReceiveEphemeral(ephemeral_message) => {
                self.react_to_ephemeral_message(ephemeral_message).await;
            }
        }
    }

    // 🧑 "make it work for three or more people reliably"
    /// Saves the document. Runs before every file write, so that a daemon killed at any moment
    /// restarts with a document at least as new as its files. With files newer than the document,
    /// the daemon shared their text again and a live trial showed duplicated lines for everyone.
    fn persist(&mut self) {
        let persistence_file = self.app_config.base_dir.join(".teamtype/doc");
        if self.save_fully {
            debug!("Persisting CRDT document fully.");
            let bytes = self.crdt_doc.save();
            sandbox::write_file(&self.app_config.base_dir, &persistence_file, &bytes)
                .unwrap_or_else(|_| {
                    panic!("Failed to persist to '{}'", persistence_file.display())
                });
            self.save_fully = false;
        } else {
            debug!("Persisting CRDT document incrementally.");
            let bytes = self.crdt_doc.save_incremental();
            sandbox::append_file(&self.app_config.base_dir, &persistence_file, &bytes)
                .unwrap_or_else(|_| {
                    panic!("Failed to persist to '{}'", persistence_file.display())
                });
        }
    }

    fn open_files_list(&self) -> PathBuf {
        self.app_config.base_dir.join(".teamtype/open-files")
    }

    fn save_files_open_in_editors(&self) {
        let lines: Vec<String> = self
            .files_open_in_editors
            .iter()
            .map(|file_path| format!("{}\n", file_path.display()))
            .collect();
        let lines = lines.concat();
        sandbox::write_file(
            &self.app_config.base_dir,
            &self.open_files_list(),
            lines.as_bytes(),
        )
        .unwrap_or_else(|err| panic!("Failed to save the list of open files: {err}"));
    }

    /// Writes files that no editor saves itself any more, and drops closed files from the list.
    fn release_files(&mut self) {
        let files: Vec<RelativePath> = self.files_open_in_editors.iter().cloned().collect();
        let mut changed = false;
        for file_path in &files {
            self.write_file(file_path);
            if self.owns(file_path) {
                self.files_open_in_editors.remove(file_path);
                changed = true;
            }
        }
        if changed {
            self.save_files_open_in_editors();
        }
    }

    /// After a crash, files that were open in an editor may differ from the saved document on disk,
    /// which holds what was shared. Reading them from disk instead shared their text again, which
    /// a live trial showed as duplicated lines for everyone.
    fn restore_files_left_open(&mut self) {
        let Ok(bytes) = sandbox::read_file(&self.app_config.base_dir, &self.open_files_list())
        else {
            return;
        };
        for line in String::from_utf8_lossy(&bytes).lines() {
            let file_path = RelativePath::new(line);
            if self.crdt_doc.file_exists(&file_path) {
                self.write_file(&file_path);
            }
        }
        self.save_files_open_in_editors();
    }

    fn absolute_path_for_file_path(&self, file_path: &RelativePath) -> AbsolutePath {
        AbsolutePath::from_parts(&self.app_config.base_dir, file_path)
            .expect("base_dir should be absolute")
    }

    // Returns the messages to send back to the editor which made the request.
    async fn react_to_message_from_editor(
        &mut self,
        editor_id: EditorId,
        message: &EditorProtocolMessageFromEditor,
    ) -> Result<Vec<EditorProtocolMessageToEditor>, EditorProtocolMessageError> {
        // First, convert the editor message into a component message (+ transformed edits from the
        // OT server).
        let (inside_message, mut messages_to_editor) = self
            .editor_connections
            .get_mut(&editor_id)
            .expect("Could not get editor connection")
            .0
            .message_from_editor(message)?;

        // Then, forward them to the "core", and get back component messages that should be
        // returned to the editor (because, for example, it opened a file with a not up-to-date
        // content.)
        let component_messages_to_editor = self
            .process_component_message(Some(editor_id), &inside_message)
            .await;

        // And finally, send these component messages back to the editor connection (pass them
        // through the OT server), to retrieve raw messages for the editor.
        let mut more_messages_to_editor =
            self.process_in_editor(editor_id, component_messages_to_editor);

        messages_to_editor.append(&mut more_messages_to_editor);

        Ok(messages_to_editor)
    }

    #[must_use]
    fn cursor_id(&self, editor_id: EditorId) -> String {
        self.crdt_doc.actor_id() + "-" + editor_id.to_string().as_str()
    }

    async fn handle_message_from_editor(&mut self, editor_id: EditorId, message: IncomingMessage) {
        // A failed send removes the editor while its later messages may still be queued; a live
        // trial crashed the daemon this way when a client disconnected right after its requests.
        if !self.editor_connections.contains_key(&editor_id) {
            debug!("Ignoring message from removed editor #{editor_id}.");
            return;
        }
        match message {
            IncomingMessage::Request { id, payload } => {
                let result = self.react_to_message_from_editor(editor_id, &payload).await;
                match result {
                    Err(error) => {
                        error!("Error for JSON-RPC request: {:?}", error);
                        self.send_to_editor_client(
                            &editor_id,
                            OutgoingMessage::Response(JSONRPCResponse::RequestError {
                                id: Some(id),
                                error,
                            }),
                        )
                        .await;
                    }
                    Ok(messages) => {
                        self.send_to_editor_client(
                            &editor_id,
                            OutgoingMessage::Response(JSONRPCResponse::RequestSuccess {
                                id,
                                result: "success".into(),
                            }),
                        )
                        .await;
                        for message in messages {
                            self.send_to_editor_client(
                                &editor_id,
                                OutgoingMessage::Notification(message),
                            )
                            .await;
                        }
                    }
                }
            }
            IncomingMessage::Notification { payload } => {
                let _ = self.react_to_message_from_editor(editor_id, &payload).await;
            }
        }
    }

    fn handle_watcher_event(&mut self, watcher_event: &WatcherEvent) {
        let relative_file_path =
            RelativePath::try_from_path(&self.app_config.base_dir, &watcher_event.file_path)
                .expect("Watcher event should have a path within the base directory");

        if vcs_lock::is_internal(&relative_file_path) {
            return;
        }
        if vcs_lock::vcs_dir_of(&relative_file_path).is_some() {
            let disk = match sandbox::read_file(&self.app_config.base_dir, &watcher_event.file_path)
            {
                Ok(bytes) => Some(bytes),
                // Being replaced right now; the rescan that follows the event sees the result.
                Err(_) if watcher_event.file_path.exists() => return,
                Err(_) => None,
            };
            self.local_vcs_change(&relative_file_path, disk);
            return;
        }
        if self.owns(&relative_file_path) {
            match watcher_event.event_type {
                WatcherEventType::Created | WatcherEventType::Changed => {
                    self.file_created_or_changed(&relative_file_path);
                }
                WatcherEventType::Removed => {
                    self.file_removed(&relative_file_path);
                }
            }
        }
    }

    fn file_removed(&mut self, relative_file_path: &RelativePath) {
        if self.crdt_doc.file_exists(relative_file_path) {
            self.note_git_activity();
        }
        self.remove_file(relative_file_path);
        let _ = self.doc_changed_ping_tx.send(());
    }

    // We react to file creations and changes in the same way because macOS sometimes
    // registers a creation when the file is only changed. We check whether or not the CRDT
    // contains the file already in the `update_text` method anyway.
    fn file_created_or_changed(&mut self, relative_file_path: &RelativePath) {
        let file_path = self.absolute_path_for_file_path(relative_file_path);
        let new_content = match sandbox::read_file(&self.app_config.base_dir, &file_path) {
            Ok(content) => content,
            Err(e) => {
                warn!(
                    "The file watcher noticed a file creation/change for {relative_file_path}, \
                    but we couldn't read it: {e} (probably it was deleted after the change?)"
                );
                return;
            }
        };
        if self.doc_bytes(relative_file_path).as_deref() != Some(new_content.as_slice()) {
            self.note_git_activity();
        }
        if let Ok(new_content) = String::from_utf8(new_content.clone()) {
            self.crdt_doc.update_text(&new_content, relative_file_path);
            // TODO: Once we get back to processing file changes while editors have it
            // open, send the delta returned by update_text to editors.
        } else {
            self.crdt_doc
                .set_file(document::Content::Bytes(new_content), relative_file_path);
        }
        let _ = self.doc_changed_ping_tx.send(());
    }

    #[must_use]
    fn apply_sync_message_to_doc(
        &mut self,
        message: AutomergeSyncMessage,
        peer_state: &mut SyncState,
    ) -> Vec<Patch> {
        let patches = self
            .crdt_doc
            .receive_sync_message_log_patches(message, peer_state);
        let _ = self.doc_changed_ping_tx.send(());
        patches
    }

    #[must_use]
    fn get_heads(&mut self) -> Vec<ChangeHash> {
        self.crdt_doc.get_heads()
    }

    #[must_use]
    fn random_delta(&self) -> TextDelta {
        let Some(document::Content::String(text)) =
            self.current_file_content(&RelativePath::new(TEST_FILE_PATH))
        else {
            panic!("Should have initialized text before performing random edit");
        };
        let mut rng = rand::rng();
        let options = ["d", "ü", "🥕", "💚", "\n"];
        let random_text: String = repeat_with(|| options[rng.random_range(0..options.len())])
            .take(4)
            .collect();
        let text_length = text.chars().count();
        let random_position = rng.random_range(0..=text_length);

        let mut delta = TextDelta::default();
        delta.retain(random_position);
        delta.insert(&random_text);

        // TODO: Delete the end/beginning of the content on purpose sometimes!
        // Goal is to make "more critical" edits more likely. Like an "inverted" gauss curve :D
        let mut deletion_length = 0;
        if (text_length - random_position) > 0 {
            deletion_length = rng.random_range(0..(text_length - random_position));
            deletion_length = deletion_length.min(3);
        }
        delta.delete(deletion_length);

        delta
    }

    async fn send_to_editor_client(&mut self, editor_id: &EditorId, message: OutgoingMessage) {
        let Some(connection) = self.editor_connections.get_mut(editor_id) else {
            return;
        };

        connection.1.send(message).await.unwrap_or_else(|err| {
            error!("Failed to send message to editor: {err} Removing editor.");
            self.editor_connections.remove(editor_id);
            self.release_files();
        });
    }

    fn write_files_changed_in_file_deltas(&mut self, file_deltas: &[FileTextDelta]) {
        // Collect file paths into a set, so we don't write files multiple times on complex
        // patches.
        let mut file_paths = HashSet::new();
        for FileTextDelta { file_path, .. } in file_deltas {
            file_paths.insert(file_path);
        }

        for file_path in file_paths {
            self.write_file(file_path);
        }
    }

    // 🧑 "make it work for three or more people reliably"
    /// Writes the file to disk, unless an open editor saves it itself: a second writer made VS
    /// Code's saves fail with "File Modified Since" in a live trial. Other open files are written,
    /// so that tools reading the disk, such as agents, see the shared text.
    fn write_file(&mut self, file_path: &RelativePath) {
        if self.editor_saves(file_path) {
            return;
        }
        if let Some(document::Content::String(text)) = self.current_file_content(file_path) {
            let bytes = text.clone().into_bytes();
            self.ensure_file_has_bytes(file_path, &bytes);
        } else {
            warn!(
                "Failed to get content of file '{file_path}' when writing to disk. Key should have existed?"
            );
        }
    }

    fn ensure_file_has_bytes(&mut self, file_path: &RelativePath, bytes: &[u8]) {
        if vcs_lock::is_internal(file_path) {
            return;
        }
        let abs_path = self.absolute_path_for_file_path(file_path);
        if sandbox::exists(&self.app_config.base_dir, &abs_path)
            .expect("Failed to check for file existence before writing to it")
        {
            // Special case: If we want to write a .git/objects/... file, and there's one already
            // there, assume that it's content will be okay. We do this because Git marks object
            // files as read-only, and we'd need to force-overwrite it. But because the objects are
            // content-addressable, its content should be fine anyway.
            if file_path.starts_with(".git/objects") {
                debug!("Not trying to replace existing file in .git/objects.");
                return;
            }

            if let Ok(current_bytes) = sandbox::read_file(&self.app_config.base_dir, &abs_path) {
                if bytes == current_bytes {
                    debug!("File content is already the desired one, not writing.");
                    return;
                }
            } else {
                debug!("Failed to read {abs_path} to check for equal content before writing.");
            }
        } else {
            info!("Creating file {file_path}.");
        }

        if self.persist {
            self.persist();
        }
        sandbox::write_file(&self.app_config.base_dir, &abs_path, bytes)
            .unwrap_or_else(|err| panic!("Failed to write to file {abs_path}: {err}"));
    }

    fn read_current_content_from_dir(&mut self, init: bool) {
        debug!("Reading current contents from disk (init: {init}).");
        let mut on_disk: HashSet<RelativePath> = HashSet::default();
        for file_path in sandbox::enumerate_non_ignored_files(&self.app_config) {
            match sandbox::read_file(&self.app_config.base_dir, &file_path) {
                Ok(bytes) => {
                    let relative_file_path =
                        RelativePath::try_from_path(&self.app_config.base_dir, &file_path)
                            .expect("Walked file path should be within base directory");
                    if vcs_lock::is_internal(&relative_file_path) {
                        continue;
                    }
                    if vcs_lock::vcs_dir_of(&relative_file_path).is_some() {
                        on_disk.insert(relative_file_path.clone());
                        if init {
                            self.vcs_known
                                .insert(relative_file_path, vcs_files::hash(&bytes));
                        } else {
                            self.local_vcs_change(&relative_file_path, Some(bytes));
                        }
                        continue;
                    }
                    if self.owns(&relative_file_path) {
                        if let Ok(text) = String::from_utf8(bytes.clone()) {
                            if init {
                                self.crdt_doc.set_file(
                                    document::Content::String(text.clone()),
                                    &relative_file_path,
                                );
                            } else {
                                self.crdt_doc.update_text(&text, &relative_file_path);
                            }
                        } else {
                            self.crdt_doc
                                .set_file(document::Content::Bytes(bytes), &relative_file_path);
                        }
                    }
                }
                Err(e) => {
                    warn!("Failed to read file '{}': {e}", file_path.display());
                }
            }
        }

        for relative_file_path in self.crdt_doc.files() {
            let absolute_file_path = self.absolute_path_for_file_path(&relative_file_path);
            if !sandbox::exists(&self.app_config.base_dir, &absolute_file_path)
                .expect(
                    "Should have been able to check for file existence while reading current directory content"
                )
                && self.owns(&relative_file_path)
                && !vcs_lock::is_internal(&relative_file_path)
            {
                warn!(
                        "File {relative_file_path} exists in the CRDT, but not on disk. Deleting from CRDT."
                    );
                self.remove_file(&relative_file_path);
            }
        }
        if !init {
            let removed: Vec<RelativePath> = self
                .vcs_known
                .keys()
                .filter(|path| !on_disk.contains(*path))
                .cloned()
                .collect();
            for path in removed {
                self.local_vcs_change(&path, None);
            }
        }
        let _ = self.doc_changed_ping_tx.send(());
    }

    /// Handles a local change to a version-control file, whose content on disk is now `disk`:
    /// sends it to the peers if we may change version control.
    fn local_vcs_change(&mut self, file_path: &RelativePath, disk: Option<Vec<u8>>) {
        if !self.app_config.sync_vcs || !self.vcs_ready || vcs_lock::is_internal(file_path) {
            return;
        }
        let hash = disk.as_deref().map(vcs_files::hash);
        if self.vcs_known.get(file_path).copied() == hash {
            // Nothing changed, or this is our own write of a peer's change.
            return;
        }
        if let Holder::Other(name) = self.git_lock.holder(&self.crdt_doc) {
            // Kept back: Git may be waiting in its hook for the lock, and the rescan when we get
            // it sends the change.
            debug!("Not sharing your change to {file_path} yet: {name} holds the Git lock.");
            return;
        }
        // Without the hook, for example with `core.hooksPath` set, Git changes are sent while
        // nobody else holds the lock, and ask for it.
        self.note_git_activity();
        match hash {
            Some(hash) => self.vcs_known.insert(file_path.clone(), hash),
            None => self.vcs_known.remove(file_path),
        };
        let _ = self.vcs_tx.send(VcsMessage::Changes {
            origin: self.git_lock.peer().to_owned(),
            files: vec![(file_path.display().to_string(), disk)],
        });
    }

    /// Our version-control files on disk.
    fn local_vcs_files(&self) -> Vec<vcs_files::VcsFile> {
        sandbox::enumerate_non_ignored_files(&self.app_config)
            .into_iter()
            .filter_map(|path| {
                let relative =
                    RelativePath::try_from_path(&self.app_config.base_dir, &path).ok()?;
                if vcs_lock::vcs_dir_of(&relative).is_none() || vcs_lock::is_internal(&relative) {
                    return None;
                }
                let bytes = sandbox::read_file(&self.app_config.base_dir, &path).ok()?;
                Some((relative.display().to_string(), Some(bytes)))
            })
            .collect()
    }

    fn receive_vcs(&mut self, message: VcsMessage) {
        match &message {
            VcsMessage::Changes { origin, files } => {
                if origin == self.git_lock.peer() {
                    return;
                }
                for file in files {
                    self.write_vcs_file(file);
                }
                if self.git_lock.is_sharer() {
                    // Relay to the other peers.
                    let _ = self.vcs_tx.send(message);
                }
            }
            VcsMessage::Snapshot { files, last } => {
                if self.git_lock.is_sharer() {
                    return;
                }
                for file in files {
                    self.write_vcs_file(file);
                    self.vcs_snapshot_paths.insert(RelativePath::new(&file.0));
                }
                if *last {
                    // Joining makes our version-control files the sharer's.
                    let snapshot = std::mem::take(&mut self.vcs_snapshot_paths);
                    for (path, _) in self.local_vcs_files() {
                        if !snapshot.contains(&RelativePath::new(&path)) {
                            self.write_vcs_file(&(path, None));
                        }
                    }
                    self.vcs_ready = true;
                    info!("Received the sharer's version-control files.");
                }
            }
        }
    }

    fn write_vcs_file(&mut self, (path, content): &vcs_files::VcsFile) {
        let relative = RelativePath::new(path);
        if vcs_lock::vcs_dir_of(&relative).is_none() || vcs_lock::is_internal(&relative) {
            warn!("Ignoring a peer's file outside version-control directories: {path}");
            return;
        }
        let abs_path = self.absolute_path_for_file_path(&relative);
        let base_dir = &self.app_config.base_dir;
        let result = match content {
            Some(bytes) => {
                if std::fs::read(&*abs_path).is_ok_and(|current| current == *bytes) {
                    Ok(())
                } else {
                    // Git makes some files read-only, so replace rather than overwrite.
                    if abs_path.exists() {
                        let _ = sandbox::remove_file(base_dir, &abs_path);
                    }
                    sandbox::write_file(base_dir, &abs_path, bytes)
                }
            }
            None if abs_path.exists() => sandbox::remove_file(base_dir, &abs_path),
            None => Ok(()),
        };
        if let Err(err) = result {
            warn!("Failed to write the peer's {path}: {err}");
        }
        match content {
            Some(bytes) => self.vcs_known.insert(relative, vcs_files::hash(bytes)),
            None => self.vcs_known.remove(&relative),
        };
    }

    fn doc_bytes(&self, file_path: &RelativePath) -> Option<Vec<u8>> {
        match self.current_file_content(file_path) {
            Some(document::Content::String(text)) => Some(text.clone().into_bytes()),
            Some(document::Content::Bytes(bytes)) => Some(bytes.clone()),
            None => None,
        }
    }

    /// A stable ID for this peer in the Git lock. Unlike the document's actor ID, it survives
    /// restarts, so a restarted peer still holds its lock.
    fn load_peer_id(&self) -> String {
        let path = self.app_config.base_dir.join(".teamtype/peer-id");
        if let Ok(bytes) = sandbox::read_file(&self.app_config.base_dir, &path)
            && let Ok(id) = String::from_utf8(bytes)
            && !id.trim().is_empty()
        {
            return id.trim().to_owned();
        }
        let id: String = repeat_with(|| format!("{:02x}", rand::rng().random::<u8>()))
            .take(16)
            .collect();
        if let Err(err) = sandbox::write_file(&self.app_config.base_dir, &path, id.as_bytes()) {
            warn!("Failed to save this peer's ID to {}: {err}", path.display());
        }
        id
    }

    /// Installs the Git hook that asks for the lock, unless the repository has its own.
    fn install_git_hook(&self) {
        let hook = self.app_config.base_dir.join(vcs_lock::HOOK);
        if !self.app_config.sync_vcs || !hook.parent().is_some_and(Path::is_dir) {
            return;
        }
        let Ok(teamtype) = std::env::current_exe() else {
            return;
        };
        // Linux names a running binary that was since replaced "<path> (deleted)"; the new
        // binary at the path is the one to run.
        let teamtype = PathBuf::from(
            teamtype
                .to_string_lossy()
                .trim_end_matches(" (deleted)")
                .to_owned(),
        );
        let script = vcs_lock::hook_script(&teamtype);
        match std::fs::read_to_string(&hook) {
            Ok(existing) if existing == script => return,
            Ok(existing) if !existing.contains("Installed by teamtype") => {
                warn!(
                    "{} exists, so Git commands do not ask for the Git lock.",
                    hook.display()
                );
                return;
            }
            _ => {}
        }
        let installed = std::fs::write(&hook, script)
            .and_then(|()| std::fs::set_permissions(&hook, std::fs::Permissions::from_mode(0o755)));
        if let Err(err) = installed {
            warn!("Failed to install {}: {err}", hook.display());
        }
    }

    fn note_git_activity(&mut self) {
        if self.app_config.sync_vcs
            && self
                .git_lock
                .note_activity(&mut self.crdt_doc, false)
                .is_some()
        {
            let _ = self.doc_changed_ping_tx.send(());
        }
    }

    /// Runs the Git lock's timers, answers `teamtype git-lock`, and installs the hook once the
    /// repository arrived.
    fn tick_git_lock(&mut self) {
        if !self.app_config.sync_vcs {
            return;
        }
        let request_file = self.app_config.base_dir.join(vcs_lock::REQUEST_FILE);
        let request = std::fs::metadata(&request_file)
            .and_then(|metadata| metadata.modified())
            .ok();
        if let Some(request) = request
            && self
                .git_lock_request
                .is_none_or(|(handled, _)| handled != request)
            && let Some(nonce) = self.git_lock.note_activity(&mut self.crdt_doc, true)
        {
            self.git_lock_request = Some((request, nonce));
            let _ = self.doc_changed_ping_tx.send(());
        }
        let held = self.git_lock.holder(&self.crdt_doc) == Holder::Me;
        if self.git_lock.tick(&mut self.crdt_doc) {
            let _ = self.doc_changed_ping_tx.send(());
        }
        if !held && self.git_lock.holder(&self.crdt_doc) == Holder::Me {
            // Let in the version-control changes we kept back.
            self.read_current_content_from_dir(false);
        }
        // Answer a request only once the sharer confirmed it, which no other peer can get at the
        // same time.
        let holder = match (self.git_lock.holder(&self.crdt_doc), self.git_lock_request) {
            (Holder::Me, Some((_, nonce))) if !self.git_lock.confirmed(&self.crdt_doc, nonce) => {
                Holder::Nobody
            }
            (holder, _) => holder,
        };
        let status =
            vcs_lock::status_line(&holder, self.git_lock_request.map(|(request, _)| request));
        let status_file = self.app_config.base_dir.join(vcs_lock::STATUS_FILE);
        if std::fs::read_to_string(&status_file).ok().as_deref() != Some(status.as_str())
            && let Err(err) = std::fs::write(&status_file, &status)
        {
            warn!("Failed to write {}: {err}", status_file.display());
        }
        self.install_git_hook();
    }

    fn current_file_content(&self, file_path: &RelativePath) -> Option<&document::Content> {
        self.crdt_doc.current_file_content(file_path)
    }

    fn file_content_at(&self, file_path: &RelativePath, heads: &[ChangeHash]) -> Result<String> {
        self.crdt_doc.file_content_at(file_path, heads)
    }

    fn remove_file(&mut self, file_path: &RelativePath) {
        if self.owns(file_path) {
            self.crdt_doc.remove_file(file_path);
        } else {
            // TODO: Once we remove the concept of ownership entirely, make sure to send proper
            // ComponentMessage to the editors that remove their entire content.
        }
    }

    /// Called when a component message is sent "into the core".
    /// Returns the component messages to send back to the editor that sent the component message.
    /// `from_editor` must be `None` if the component message originates from the "CRDT component".
    async fn process_component_message(
        &mut self,
        from_editor: Option<EditorId>,
        message: &ComponentMessage,
    ) -> Vec<ComponentMessage> {
        let mut to_editor = vec![];

        match message {
            ComponentMessage::Open { file_path, content } => {
                if self.files_open_in_editors.insert(file_path.clone()) {
                    self.save_files_open_in_editors();
                }
                if let Some(document::Content::String(crdt_content)) =
                    self.current_file_content(file_path)
                {
                    // We want to compare the content sent along with the "open" with the content
                    // that's known to the CRDT.
                    let chunks = dissimilar::diff(content, crdt_content);
                    if let [] | [dissimilar::Chunk::Equal(_)] = chunks.as_slice() {
                        // The contents match, nothing to do.
                    } else {
                        // The editor's content and the CRDT content differ. Update the editor to
                        // match.
                        let text_delta: TextDelta = chunks.into();
                        let update_message = ComponentMessage::Edit {
                            file_path: file_path.clone(),
                            delta: text_delta,
                        };

                        to_editor.push(update_message);
                    }
                } else {
                    // The file doesn't exist yet - create it in the Automerge document.
                    self.crdt_doc
                        .set_file(document::Content::String(content.clone()), file_path);
                    let _ = self.doc_changed_ping_tx.send(());
                    self.write_file(file_path);
                }
            }
            ComponentMessage::Close { .. } => self.release_files(),
            ComponentMessage::Edit { file_path, delta } => {
                if from_editor.is_some() {
                    self.note_git_activity();
                }
                self.crdt_doc.apply_delta_to_doc(delta, file_path).expect("Failed to apply delta to document while handling edit ComponentMessage. Probably the delta doesn't fit the document content.");
                let _ = self.doc_changed_ping_tx.send(());
                self.write_file(file_path);
            }
            ComponentMessage::Cursor {
                cursor_id,
                cursor_state,
            } => {
                let next_sequence_number =
                    if let Some(old_cursor_state) = self.ephemeral_states.get_mut(cursor_id) {
                        old_cursor_state.sequence_number + 1
                    } else {
                        0
                    };

                let new_cursor_state = EphemeralMessage {
                    cursor_id: cursor_id.clone(),
                    sequence_number: next_sequence_number,
                    cursor_state: cursor_state.clone(),
                };

                self.ephemeral_states
                    .insert(cursor_id.clone(), new_cursor_state.clone());

                let _ = self.ephemeral_message_tx.send(new_cursor_state);
            }
        }

        self.broadcast_to_editors(from_editor, message).await;

        to_editor
    }

    // Send component message to all editors, excluding `exclude_id`.
    async fn broadcast_to_editors(
        &mut self,
        exclude_id: Option<EditorId>,
        message: &ComponentMessage,
    ) {
        let editor_ids: Vec<EditorId> = self.editor_connections.keys().copied().collect();
        for editor_id in editor_ids {
            if Some(editor_id) == exclude_id {
                continue;
            }

            self.send_to_editor(editor_id, message).await;
        }
    }

    // Returns the protocol messages that should be sent to the editor.
    #[must_use]
    fn process_in_editor(
        &mut self,
        editor_id: EditorId,
        messages: Vec<ComponentMessage>,
    ) -> Vec<EditorProtocolMessageToEditor> {
        let mut all_responses = vec![];
        // A failed send while handling this editor's message may have removed it.
        let Some((connection, _)) = self.editor_connections.get_mut(&editor_id) else {
            return all_responses;
        };

        for message in messages {
            let mut responses = connection.message_from_inside(&message);
            all_responses.append(&mut responses);
        }

        all_responses
    }

    async fn send_to_editor(&mut self, editor_id: EditorId, message: &ComponentMessage) {
        let messages_to_editor = self.process_in_editor(editor_id, vec![message.clone()]);

        for message_to_editor in messages_to_editor {
            self.send_to_editor_client(
                &editor_id,
                OutgoingMessage::Notification(message_to_editor),
            )
            .await;
        }
    }

    async fn react_to_ephemeral_message(&mut self, new_ephemeral_message: EphemeralMessage) {
        let cursor_id = new_ephemeral_message.cursor_id.clone();
        let cursor_state = new_ephemeral_message.cursor_state.clone();

        if let Some(existing_state) = self.ephemeral_states.get_mut(&cursor_id)
            && new_ephemeral_message.sequence_number <= existing_state.sequence_number
        {
            // We've already seen a newer ephemeral message for this cursor_id, thus ignoring
            // this older one.
            return;
        }
        self.ephemeral_states
            .insert(cursor_id.clone(), new_ephemeral_message.clone());

        // Broadcast to peers.
        let _ = self.ephemeral_message_tx.send(new_ephemeral_message);

        // Broadcast to editors.
        self.broadcast_to_editors(
            None,
            &ComponentMessage::Cursor {
                cursor_id,
                cursor_state,
            },
        )
        .await;
    }

    async fn maybe_delete_cursor_position(&mut self, cursor_id: &CursorId) {
        let message = ComponentMessage::Cursor {
            cursor_id: cursor_id.clone(),
            cursor_state: CursorState {
                name: None,
                // NOTE: The "cursor" message doesn't have a specific
                // deletion mechanism. We get around this by setting it to an empty file path,
                // which means it will disappear from any previous file path.
                file_path: RelativePath::new(""),
                ranges: vec![],
            },
        };

        self.process_component_message(None, &message).await;

        self.ephemeral_states.remove(cursor_id);
    }

    async fn run(&mut self) {
        while let Some(message) = self.doc_message_rx.recv().await {
            self.handle_message(message).await;
        }
        debug!("Channel towards document handle has been closed (probably shutting down).");
    }
}

/// This handle knows how to talk to the `DocumentActor` and provides an interface for doing so.
///
/// The main interfaces for doing so is through sending `DocMessage`s with `send_message`.
/// An alternative pathway is to subscribe to documents changes through `subscribe_document_changes`.
///
/// The rest of the methods are used for instrumentation (e.g. by the fuzzer).
#[derive(Clone)]
#[must_use]
pub struct DocumentActorHandle {
    doc_message_tx: DocMessageSender,
    doc_changed_ping_tx: DocChangedSender,
    ephemeral_message_tx: EphemeralMessageSender,
    vcs_tx: broadcast::Sender<VcsMessage>,
    is_host: bool,
    base_dir: PathBuf,
    next_id: Arc<AtomicUsize>,
}

impl DocumentActorHandle {
    pub fn new(app_config: &AppConfig, init: bool, is_host: bool, persist: bool) -> Self {
        // The document task will receive messages on this channel.
        let (doc_message_tx, doc_message_rx) = mpsc::channel(1);

        // The document task will send a ping on this channel whenever it changes.
        // The sync tasks will subscribe to it, and react to it by syncing with the peers.
        let (doc_changed_ping_tx, _doc_changed_ping_rx) = broadcast::channel::<()>(1);

        // The document actor will send ephemeral messages for other peers to this channel.
        let (ephemeral_message_tx, _ephemeral_message_rx) =
            broadcast::channel::<EphemeralMessage>(100);

        let mut actor = DocumentActor::new(
            doc_message_rx,
            doc_changed_ping_tx.clone(),
            ephemeral_message_tx.clone(),
            app_config.clone(),
            init,
            is_host,
            persist,
        );

        let vcs_tx = actor.vcs_tx.clone();
        tokio::spawn(async move { actor.run().await });

        Self {
            doc_message_tx,
            doc_changed_ping_tx,
            ephemeral_message_tx,
            vcs_tx,
            is_host,
            base_dir: app_config.base_dir.clone(),
            next_id: Arc::default(),
        }
    }

    /// The TCP and socket connections will send messages through this when they receive something.
    pub async fn send_message(&self, message: DocMessage) {
        self.doc_message_tx
            .send(message)
            .await
            .expect("DocumentActor task has been killed");
    }

    #[must_use]
    pub fn subscribe_document_changes(&self) -> DocChangedReceiver {
        self.doc_changed_ping_tx.subscribe()
    }

    #[must_use]
    pub fn subscribe_ephemeral_messages(&self) -> EphemeralMessageReceiver {
        self.ephemeral_message_tx.subscribe()
    }

    pub fn subscribe_vcs_messages(&self) -> broadcast::Receiver<VcsMessage> {
        self.vcs_tx.subscribe()
    }

    #[must_use]
    pub const fn is_host(&self) -> bool {
        self.is_host
    }

    #[must_use]
    pub fn base_dir(&self) -> &Path {
        &self.base_dir
    }

    /// This document's history ID, and whether it has any files.
    pub async fn history_id(&self) -> (Option<String>, bool) {
        let (response_tx, response_rx) = oneshot::channel();
        self.send_message(DocMessage::HistoryId { response_tx })
            .await;
        response_rx.await.unwrap_or((None, false))
    }

    /// The sharer's version-control files for a peer that just connected, or none elsewhere.
    pub async fn vcs_snapshot(&self) -> Vec<VcsMessage> {
        if !self.is_host {
            return vec![];
        }
        let (response_tx, response_rx) = oneshot::channel();
        self.send_message(DocMessage::VcsSnapshot { response_tx })
            .await;
        response_rx.await.unwrap_or_default()
    }

    pub async fn content(&self) -> Option<document::Content> {
        let (send, recv) = oneshot::channel();
        let message = DocMessage::GetContent { response_tx: send };
        // Ignore send errors, because recv.await will fail anyway.
        let _ = self.doc_message_tx.send(message).await;
        recv.await.expect("DocumentActor task has been killed")
    }

    pub async fn apply_random_delta(&self) {
        let message = DocMessage::RandomEdit;
        self.doc_message_tx
            .send(message)
            .await
            .expect("Failed to send random edit to document task");
    }

    #[must_use]
    pub fn next_editor_id(&self) -> EditorId {
        self.next_id.fetch_add(1, Ordering::Relaxed)
    }
}

#[must_use]
pub struct Daemon {
    pub document_handle: DocumentActorHandle,
    pub address: String,
    socket_path: PathBuf,
    app_config: AppConfig,
    #[expect(dead_code)]
    // We need to store the connection manager in order to keep the connection alive.
    connection_manager: peer::ConnectionManager,
}

impl Daemon {
    // Launch the daemon. Optionally, connect to given peer.
    pub async fn new(app_config: AppConfig, init: bool, persist: bool) -> Result<Self> {
        let is_host = app_config.is_host();

        let document_handle = DocumentActorHandle::new(&app_config, init, is_host, persist);

        let base_dir = &app_config.base_dir;

        // Start socket listener.
        let socket_path = base_dir
            .join(config::CONFIG_DIR)
            .join(config::DEFAULT_SOCKET_NAME);
        editor::spawn_socket_listener(&socket_path, document_handle.clone())?;

        // Start file watcher.
        spawn_file_watcher(&app_config, document_handle.clone());

        if app_config.sync_vcs {
            spawn_vcs_lock_checker(document_handle.clone());
        }

        if persist {
            // Start persister.
            spawn_persister(document_handle.clone());
        }

        // Start connection manager.
        let connection_manager =
            peer::ConnectionManager::new(&app_config, document_handle.clone(), base_dir)
                .await
                .expect("Failed to start connection manager");
        let address = connection_manager.secret_address();

        if app_config.emit_secret_address {
            info!(
                "{}",
                &docstr!(format!
                    /// Others can connect by putting the following secret address in their .teamtype/config:
                    ///
                    ///     peer={address}
                    ///
                )
            );
        }
        if app_config.emit_join_code {
            put_secret_address_into_wormhole(address, app_config.magic_wormhole_relay.clone())
                .await;
        }
        if let Some(config::Peer::SecretAddress(ref secret_address)) = app_config.peer {
            let mut n_attempts_left = INITIAL_CONNECT_ATTEMPTS;
            while let Err(err) = connection_manager.connect(secret_address.clone()).await {
                n_attempts_left -= 1;
                if n_attempts_left == 0 {
                    return Err(err.context("Failed to connect to specified peer"));
                }
                if format!("{err:#}").contains("known protocol") {
                    return Err(err.context(
                        "The sharer runs a teamtype version that cannot sync with yours; install the same build on both sides",
                    ));
                }
                warn!("Could not connect to specified peer, retrying: {err:#}");
                sleep(INITIAL_CONNECT_RETRY_DELAY).await;
            }
        }

        Ok(Self {
            document_handle,
            address: address.to_owned(),
            socket_path,
            app_config,
            connection_manager,
        })
    }
}

impl Drop for Daemon {
    fn drop(&mut self) {
        debug!("Daemon dropped, removing socket");

        sandbox::remove_file(Path::new(&self.app_config.base_dir), &self.socket_path)
            .expect("Could not remove socket");
    }
}

// Spawn a file watcher and feed its events to the document_handle.
// In addition, a short timeout after the last event, do a full re-scan, so that we don't miss any
// file changes - the watcher isn't necessarily exhaustive.
fn spawn_file_watcher(app_config: &AppConfig, document_handle: DocumentActorHandle) {
    let mut event_rx = Watcher::spawn(app_config.clone());

    tokio::spawn(async move {
        let debounce_duration = Duration::from_millis(100);

        let debounce_timer = sleep(debounce_duration);
        // Sleep does not implement the Unpin trait, so in order to use it with select!, we have to
        // pin it first (according to the documentation https://docs.rs/tokio/latest/tokio/time/struct.Sleep.html).
        tokio::pin!(debounce_timer);

        let mut rescan_required = false;

        loop {
            tokio::select! {
                maybe_event = event_rx.recv() => {
                    if let Some(watcher_event) = maybe_event {
                        document_handle
                            .send_message(DocMessage::FromWatcher(watcher_event))
                            .await;

                        debounce_timer.as_mut().reset(Instant::now() + debounce_duration);
                        rescan_required = true;
                    } else {
                        // Watcher terminated. Seems we're shutting down.
                        return;
                    }
                }

                () = &mut debounce_timer, if rescan_required => {
                    document_handle
                        .send_message(DocMessage::RescanFiles)
                        .await;
                    rescan_required = false;
                }
            }
        }
    });
}

/// Runs the Git lock's timers and answers `teamtype git-lock`.
fn spawn_vcs_lock_checker(document_handle: DocumentActorHandle) {
    tokio::spawn(async move {
        loop {
            sleep(Duration::from_millis(200)).await;
            document_handle.send_message(DocMessage::CheckVcsLock).await;
        }
    });
}

fn spawn_persister(document_handle: DocumentActorHandle) {
    tokio::spawn(async move {
        let mut doc_changed_ping_rx = document_handle.subscribe_document_changes();

        document_handle.send_message(DocMessage::Persist).await;

        loop {
            match doc_changed_ping_rx.recv().await {
                Ok(()) => {
                    // The document has changed.
                }
                Err(RecvError::Closed) => {
                    panic!("Doc changed channel has been closed");
                }
                Err(RecvError::Lagged(_)) => {
                    // This is fine, the messages in this channel are just pings.
                    // It's fine if we miss some.
                    debug!("Doc changed ping channel lagged (this is probably fine).");
                }
            }

            document_handle.send_message(DocMessage::Persist).await;

            // Alternatively to sleeping, we could use a "back channel" in the Persist
            // message, so that the daemon tells us when it's done persisting.
            sleep(Duration::from_secs(1)).await;
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    //use crate::types::factories::*;

    mod document_actor {
        use tempfile::{TempDir, tempdir};

        use super::*;
        //use tracing_test::traced_test;

        impl DocumentActor {
            // TODO: Refactor, to reuse stuff from DocumentActorHandle constructor.
            fn setup_for_testing(directory: &TempDir) -> Self {
                // The document task will receive messages on this channel.
                let (_doc_message_tx, doc_message_rx) = mpsc::channel(1);

                // The document task will send a ping on this channel whenever it changes.
                // The sync tasks will subscribe to it, and react to it by syncing with the peers.
                let (doc_changed_ping_tx, _doc_changed_ping_rx) = broadcast::channel::<()>(1);

                // The document actor will send ephemeral messages for other peers to this channel.
                let (ephemeral_message_tx, _ephemeral_message_rx) =
                    broadcast::channel::<EphemeralMessage>(100);

                Self::new(
                    doc_message_rx,
                    doc_changed_ping_tx,
                    ephemeral_message_tx,
                    AppConfig {
                        base_dir: directory.path().to_path_buf(),
                        ..Default::default()
                    },
                    true,
                    true,
                    false,
                )
            }

            fn assert_file_content(&self, file_path: &RelativePath, content: &str) {
                assert_eq!(
                    self.current_file_content(file_path),
                    Some(document::Content::String(content.to_string())).as_ref()
                );
            }
        }

        fn setup_filesystem_for_testing() -> TempDir {
            let dir = tempdir().expect("Failed to create temp directory");
            let dir_path = dir.path();
            let file1 = dir_path.join("file1");
            let file2 = dir_path.join("file2");
            let subdir = dir_path.join("sub");
            sandbox::create_dir(dir_path, &subdir).unwrap();
            let file3 = subdir.join("file3");
            sandbox::write_file(dir_path, &file1, b"content1").unwrap();
            sandbox::write_file(dir_path, &file2, b"content2").unwrap();
            sandbox::write_file(dir_path, &file3, b"content3").unwrap();
            dir
        }

        #[test]
        fn read_contents_from_dir() {
            let dir = setup_filesystem_for_testing();
            let mut actor = DocumentActor::setup_for_testing(&dir);

            actor.read_current_content_from_dir(true);

            actor.assert_file_content(&RelativePath::new("file1"), "content1");
            actor.assert_file_content(&RelativePath::new("file2"), "content2");
            actor.assert_file_content(&RelativePath::new("sub/file3"), "content3");
        }
    }
}
