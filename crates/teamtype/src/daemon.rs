// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::iter::repeat_with;
use std::path::{Path, PathBuf};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use anyhow::{Context, Result};
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
use crate::git_forward;
use crate::path::{AbsolutePath, FileUri, RelativePath};
use crate::peer;
use crate::sandbox;
use crate::types::{
    ComponentMessage, CursorId, CursorState, EphemeralMessage, FileTextDelta, PatchEffect,
    TextDelta,
};
use crate::watcher::WatcherEvent;
use crate::watcher::{Watcher, WatcherEventType};
use crate::wormhole::put_secret_address_into_wormhole;

// 🧑 "make it work for three or more people reliably"
/// One failed address lookup must not end a join: a live three-daemon trial lost a joiner that way.
const INITIAL_CONNECT_ATTEMPTS: usize = 5;
/// Identifies the sharer's history; set when the sharer starts a new one.
/// This CRDT key is not a disk path; keeping it preserves existing fork histories.
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
    GitHeads {
        response_tx: oneshot::Sender<Vec<ChangeHash>>,
    },
    GitReady {
        heads: Vec<ChangeHash>,
        response_tx: oneshot::Sender<Result<bool>>,
    },
    GitStarted {
        heads: Vec<ChangeHash>,
        response_tx: oneshot::Sender<Result<bool>>,
    },
    GitFinished {
        response_tx: oneshot::Sender<Result<()>>,
    },
    /// This document's history ID, and whether it has any files.
    HistoryId {
        response_tx: oneshot::Sender<(Option<String>, bool)>,
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
            Self::GitHeads { .. } => "GitHeads".to_string(),
            Self::GitReady { .. } => "GitReady".to_string(),
            Self::GitStarted { .. } => "GitStarted".to_string(),
            Self::GitFinished { .. } => "GitFinished".to_string(),
            Self::HistoryId { .. } => "HistoryId".to_string(),
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
    /// Last bytes read or written, used as the base of concurrent disk edits.
    disk_content: HashMap<RelativePath, Vec<u8>>,
    disk_edits: Vec<ComponentMessage>,
    git_running: bool,
    deferred_writes: HashSet<RelativePath>,
    deferred_removals: HashSet<RelativePath>,
    /// Displaced files whose bytes are merged into the document but not yet saved with it.
    displaced_unsaved: Vec<PathBuf>,
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
        // If there is a persisted version in base_dir/.teamtypev/doc, load it.
        // TODO: Pull out ".teamtypev" string into a constant.
        let persistence_file = app_config.base_dir.join(".teamtypev/doc");
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
            Document::try_load(&bytes).unwrap_or_else(|error| {
                // Never crash-loop on a damaged save: keep it for inspection and start empty.
                error!("Persisted document is unreadable ({error:#}); setting it aside.");
                let _ = sandbox::rename_file(
                    &app_config.base_dir,
                    &persistence_file,
                    &app_config.base_dir.join(".teamtypev/doc.corrupt"),
                );
                Document::default()
            })
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
            disk_content: HashMap::new(),
            disk_edits: Vec::new(),
            git_running: false,
            deferred_writes: HashSet::new(),
            deferred_removals: HashSet::new(),
            displaced_unsaved: Vec::new(),
        };
        git_forward::remove_old_hook(&s.app_config.base_dir);
        for path in s.crdt_doc.files() {
            if git_forward::excluded(&path) && path != RelativePath::new(HISTORY_ID) {
                s.crdt_doc.remove_file(&path);
            }
        }
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
                let left_open: HashSet<RelativePath> =
                    sandbox::read_file(&s.app_config.base_dir, &s.open_files_list())
                        .map(|bytes| {
                            String::from_utf8_lossy(&bytes)
                                .lines()
                                .map(RelativePath::new)
                                .collect()
                        })
                        .unwrap_or_default();
                s.check_files_left_open();
                let pending_before = s.read_pending();
                s.drop_staged_displaced();
                s.apply_pending_writes(&left_open);
                s.recover_displaced(&pending_before);
            }
            s.read_current_content_from_dir(init);
        } else if is_host {
            s.read_current_content_from_dir(true);
        }

        s
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
        // Proof assumption (verification/editor_conn_proof): nothing is queued between messages, so
        // deltas reach editors in the order the document changed.
        debug_assert!(
            self.disk_edits.is_empty(),
            "disk edits left queued from the previous message"
        );
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
                if !self.git_running {
                    for path in std::mem::take(&mut self.deferred_writes) {
                        self.write_file(&path);
                    }
                }
            }
            DocMessage::GitHeads { response_tx } => {
                self.read_current_content_from_dir(false);
                let _ = response_tx.send(self.get_heads());
            }
            DocMessage::GitReady { heads, response_tx } => {
                let ready = self.crdt_doc.has_changes(&heads);
                let result = if ready && !self.git_running {
                    self.flush_git_files().map(|()| true)
                } else {
                    Ok(ready)
                };
                let _ = response_tx.send(result);
            }
            DocMessage::GitStarted { heads, response_tx } => {
                let result = self.start_git(&heads);
                let _ = response_tx.send(result);
            }
            DocMessage::GitFinished { response_tx } => {
                let result = self.finish_git();
                let _ = response_tx.send(result);
            }
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
                    .any(|path| !git_forward::excluded(path));
                let _ = response_tx.send((id, has_files));
            }
            DocMessage::Persist => {
                if let Err(error) = self.persist() {
                    error!("Could not persist shared document: {error:#}");
                }
            }
            DocMessage::ReceiveSyncMessage {
                message,
                state: mut peer_state,
                response_tx,
            } => {
                let heads_before_sync_message = self.get_heads();

                let patches = self.apply_sync_message_to_doc(message, &mut peer_state);

                let patch_effects = PatchEffect::from_crdt_patches(&patches);
                // Before any save of the document that includes these changes.
                self.mark_pending(patch_effects.iter().filter_map(|effect| match effect {
                    PatchEffect::FileChange(delta) => Some(delta.file_path.clone()),
                    PatchEffect::FileRemoval(path) | PatchEffect::FileBytes(path, _) => {
                        Some(path.clone())
                    }
                    PatchEffect::NoEffect => None,
                }));

                let mut file_deltas = vec![];

                for patch_effect in patch_effects {
                    match patch_effect {
                        PatchEffect::FileChange(file_text_delta) => {
                            file_deltas.push(file_text_delta);
                        }
                        PatchEffect::FileRemoval(file_path) => {
                            if git_forward::excluded(&file_path) {
                                continue;
                            }
                            if self.owns(&file_path) && self.crdt_doc.file_exists(&file_path) {
                                // A peer's file of the same name replaced ours; no further
                                // patch arrives for it if it is empty.
                                self.write_file(&file_path);
                            } else if self.owns(&file_path) {
                                info!("Removing file {file_path}.");
                                if self.git_running {
                                    self.deferred_removals.insert(file_path);
                                } else if let Some(bytes) = self.unhandled_outside_write(&file_path)
                                {
                                    // Changed on disk while a peer deleted it: the edit wins and is
                                    // shared again (as on restart, `apply_pending_writes`).
                                    self.merge_disk_content(&file_path, bytes);
                                } else {
                                    self.remove_disk_file(&file_path);
                                }
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
                                    .unwrap_or_default();

                                // Proof assumption: what we delete is what every editor holds.
                                #[cfg(test)]
                                for (connection, _) in self.editor_connections.values() {
                                    if let Some(text) = connection.server_text(&file_path) {
                                        assert_eq!(
                                            text, content_before_sync_message,
                                            "editor text differs from the text before the sync message"
                                        );
                                    }
                                }

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
                        PatchEffect::FileBytes(file_path, _) => {
                            self.invalidate_editor_file(&file_path);
                            self.write_file(&file_path);
                        }
                        PatchEffect::NoEffect => {}
                    }
                }

                self.write_files_changed_in_file_deltas(&file_deltas);

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
        self.send_disk_edits().await;
        debug_assert_eq!(self.disk_edits.len(), 0);
    }

    // 🧑 "make it work for three or more people reliably"
    /// Saves the document. Runs before every file write, so that a daemon killed at any moment
    /// restarts with a document at least as new as its files. With files newer than the document,
    /// the daemon shared their text again and a live trial showed duplicated lines for everyone.
    fn persist(&mut self) -> Result<()> {
        let persistence_file = self.app_config.base_dir.join(".teamtypev/doc");
        let result = if self.save_fully {
            debug!("Persisting CRDT document fully.");
            let bytes = self.crdt_doc.save();
            // Atomic: a crash while rewriting must not leave a truncated document.
            sandbox::replace_file(&self.app_config.base_dir, &persistence_file, &bytes).map(|_| ())
        } else {
            debug!("Persisting CRDT document incrementally.");
            let bytes = self.crdt_doc.save_incremental();
            sandbox::append_file(&self.app_config.base_dir, &persistence_file, &bytes)
        };
        // Saving advances Automerge's incremental cursor even when disk I/O fails.
        self.save_fully = result.is_err();
        if result.is_ok() {
            // The document now holds what the displaced files held.
            for kept in std::mem::take(&mut self.displaced_unsaved) {
                let _ = std::fs::remove_file(kept);
            }
        }
        result.with_context(|| format!("Failed to persist to '{}'", persistence_file.display()))
    }

    fn pending_list(&self) -> PathBuf {
        self.app_config.base_dir.join(".teamtypev/pending-writes")
    }

    /// Records the files the shared document changed but the disk may not yet reflect, with the
    /// bytes the disk had when the document last agreed with it (`None`: no such file). Saved
    /// before any later save of the document, so that a crash never leaves the document ahead of
    /// the disk without this record: restarting would otherwise read the stale files as outside
    /// edits that undo peers' changes, or recreate files peers deleted. The kept bytes are the
    /// base for merging whatever changed on disk meanwhile (for example by a Git command).
    fn mark_pending(&self, paths: impl IntoIterator<Item = RelativePath>) {
        if !self.persist {
            return;
        }
        let mut list = self.read_pending();
        let before = list.len();
        for path in paths {
            let base = self.disk_content.get(&path).cloned();
            list.entry(path).or_insert(base);
        }
        if list.len() != before {
            self.write_pending(&list);
        }
    }

    fn unmark_pending(&self, path: &RelativePath) {
        if !self.persist {
            return;
        }
        let mut list = self.read_pending();
        if list.remove(path).is_some() {
            self.write_pending(&list);
        }
    }

    fn read_pending(&self) -> HashMap<RelativePath, Option<Vec<u8>>> {
        sandbox::read_file(&self.app_config.base_dir, &self.pending_list())
            .ok()
            .and_then(|bytes| postcard::from_bytes::<Vec<(String, Option<Vec<u8>>)>>(&bytes).ok())
            .unwrap_or_default()
            .into_iter()
            .map(|(path, base)| (RelativePath::new(&path), base))
            .collect()
    }

    fn write_pending(&self, list: &HashMap<RelativePath, Option<Vec<u8>>>) {
        let entries: Vec<(String, Option<Vec<u8>>)> = list
            .iter()
            .map(|(path, base)| (path.display().to_string(), base.clone()))
            .collect();
        let result = postcard::to_allocvec(&entries)
            .map_err(anyhow::Error::from)
            .and_then(|bytes| {
                sandbox::replace_file(&self.app_config.base_dir, &self.pending_list(), &bytes)
            });
        if let Err(error) = result {
            error!("Could not record pending file writes: {error:#}");
        }
    }

    /// After a restart, brings files the document is ahead on up to date, before the scan could
    /// mistake them for outside edits. Whatever changed on disk since is merged with the
    /// document first, with the recorded bytes as the base. Files that were open in an editor
    /// keep the disk version.
    fn apply_pending_writes(&mut self, left_open: &HashSet<RelativePath>) {
        for (path, base) in self.read_pending() {
            if git_forward::excluded(&path) || left_open.contains(&path) {
                self.unmark_pending(&path);
                continue;
            }
            let absolute = self.absolute_path_for_file_path(&path);
            let on_disk = sandbox::read_file(&self.app_config.base_dir, &absolute).ok();
            let in_document = self.crdt_doc.file_exists(&path);
            match (on_disk, in_document) {
                (Some(bytes), true)
                    if self
                        .current_file_content(&path)
                        .is_some_and(|content| match content {
                            document::Content::String(text) => text.as_bytes() == bytes.as_slice(),
                            document::Content::Bytes(shared) => shared == &bytes,
                        }) =>
                {
                    // The write finished; only clearing the record was interrupted. Merging
                    // would apply the document's own change to itself a second time.
                    self.disk_content.insert(path.clone(), bytes);
                    self.unmark_pending(&path);
                    continue;
                }
                (Some(bytes), true) => {
                    // A file that had no base was created by the peer; Git may have made one too.
                    self.disk_content
                        .insert(path.clone(), base.unwrap_or_default());
                    self.merge_disk_content(&path, bytes);
                }
                (Some(bytes), false) if base.as_ref() != Some(&bytes) => {
                    // Changed on disk while peers deleted it: the edit wins and is shared again.
                    self.unmark_pending(&path);
                    continue;
                }
                _ => {}
            }
            if in_document {
                if let Err(error) = self.try_write_file(&path) {
                    warn!("Could not finish a write interrupted by a restart: {error:#}");
                }
            } else {
                self.remove_disk_file(&path);
            }
        }
    }

    fn open_files_list(&self) -> PathBuf {
        self.app_config.base_dir.join(".teamtypev/open-files")
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

    /// Drops closed files from the recovery list.
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

    /// Refuses recovery when files left open after a crash differ from persisted history.
    /// Never writes shared text over disk saves; differing versions require manual reconciliation.
    /// After a crash, files that were open in editors may hold saves newer than the persisted
    /// history. Never restore them from history: the disk version is kept, and the scan that
    /// follows shares it like any other edit made while teamtypev was down.
    fn check_files_left_open(&self) {
        let bytes = match sandbox::read_file(&self.app_config.base_dir, &self.open_files_list()) {
            Ok(bytes) => bytes,
            Err(err)
                if err
                    .downcast_ref::<std::io::Error>()
                    .is_some_and(|io| io.kind() == std::io::ErrorKind::NotFound) =>
            {
                return;
            }
            Err(err) => {
                warn!("Cannot read the list of files open before the last stop: {err}");
                self.save_files_open_in_editors();
                return;
            }
        };
        for line in String::from_utf8_lossy(&bytes).lines() {
            let path = RelativePath::new(line);
            let Some(content) = self.current_file_content(&path) else {
                continue;
            };
            let shared = match content {
                document::Content::String(text) => text.as_bytes(),
                document::Content::Bytes(bytes) => bytes.as_slice(),
            };
            let saved = sandbox::read_file(
                &self.app_config.base_dir,
                &self.absolute_path_for_file_path(&path),
            );
            if !saved.is_ok_and(|saved| saved == shared) {
                warn!(
                    "{line} was open in an editor when teamtypev last stopped and differs from \
                     teamtypev's history; keeping the version on disk."
                );
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
        if matches!(message, EditorProtocolMessageFromEditor::DaemonWriter {}) {
            return Ok(vec![]);
        }
        if let EditorProtocolMessageFromEditor::Save { uri } = message {
            let path = FileUri::try_from(uri.clone())
                .and_then(|uri| {
                    RelativePath::try_from_absolute(
                        &self.app_config.base_dir,
                        &uri.to_absolute_path(),
                    )
                })
                .map_err(|error| EditorProtocolMessageError {
                    code: -1,
                    message: error.to_string(),
                    data: None,
                })?;
            if !self
                .editor_connections
                .get(&editor_id)
                .is_some_and(|(connection, _)| connection.owns(&path))
            {
                return Err(EditorProtocolMessageError {
                    code: -1,
                    message: "File is not shared by this editor".into(),
                    data: None,
                });
            }
            self.file_created_or_changed(&path);
            if !matches!(
                self.current_file_content(&path),
                Some(document::Content::String(_))
            ) {
                return Err(EditorProtocolMessageError {
                    code: -1,
                    message: "The shared file is no longer UTF-8 text; reopen it before saving"
                        .into(),
                    data: None,
                });
            }
            let saved = self.try_write_file(&path);
            self.send_disk_edits().await;
            saved.map_err(|error| EditorProtocolMessageError {
                code: -1,
                message: format!("Could not save shared file: {error:#}"),
                data: None,
            })?;
            return Ok(vec![]);
        }
        if let EditorProtocolMessageFromEditor::Open { uri, .. }
        | EditorProtocolMessageFromEditor::Edit { uri, .. } = message
            && let Ok(uri) = FileUri::try_from(uri.clone())
            && let Ok(path) =
                RelativePath::try_from_absolute(&self.app_config.base_dir, &uri.to_absolute_path())
            && self.disk_content.contains_key(&path)
        {
            self.file_created_or_changed(&path);
            if matches!(message, EditorProtocolMessageFromEditor::Edit { .. })
                && !matches!(
                    self.current_file_content(&path),
                    Some(document::Content::String(_))
                )
            {
                return Err(EditorProtocolMessageError {
                    code: -1,
                    message: "The shared file is no longer UTF-8 text; reopen it before editing"
                        .into(),
                    data: None,
                });
            }
        }
        self.send_disk_edits().await;
        // Proof assumption: an editor's message sees every document change already broadcast.
        debug_assert_eq!(self.disk_edits.len(), 0);
        // First, convert the editor message into a component message (+ transformed edits from the
        // OT server).
        let (inside_message, mut messages_to_editor) = self
            .editor_connections
            .get_mut(&editor_id)
            .expect("Could not get editor connection")
            .0
            .message_from_editor(!self.git_running, message)?;

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
        if self.git_running {
            return;
        }
        let relative_file_path =
            RelativePath::try_from_path(&self.app_config.base_dir, &watcher_event.file_path)
                .expect("Watcher event should have a path within the base directory");

        if git_forward::excluded(&relative_file_path) {
            return;
        }
        {
            match watcher_event.event_type {
                WatcherEventType::Created | WatcherEventType::Changed => {
                    self.file_created_or_changed(&relative_file_path);
                    if matches!(
                        self.current_file_content(&relative_file_path),
                        Some(document::Content::String(_))
                    ) {
                        self.write_file(&relative_file_path);
                    }
                }
                WatcherEventType::Removed => {
                    let absolute = self.absolute_path_for_file_path(&relative_file_path);
                    if sandbox::exists(&self.app_config.base_dir, &absolute).unwrap_or(false) {
                        self.file_created_or_changed(&relative_file_path);
                    } else {
                        self.file_removed(&relative_file_path);
                    }
                }
            }
        }
    }

    fn file_removed(&mut self, relative_file_path: &RelativePath) {
        if self.deferred_writes.contains(relative_file_path)
            && !self.disk_content.contains_key(relative_file_path)
        {
            // A write is pending and the daemon never put this file on disk, so its absence is
            // not a deletion by the user (same rule as the rescan in `read_current_content_from_dir`).
            return;
        }
        self.remove_file(relative_file_path);
        let _ = self.doc_changed_ping_tx.send(());
    }

    // We react to file creations and changes in the same way because macOS sometimes
    // registers a creation when the file is only changed. We check whether or not the CRDT
    // contains the file already in the `update_text` method anyway.
    fn file_created_or_changed(&mut self, relative_file_path: &RelativePath) {
        if self.git_running {
            return;
        }
        let file_path = self.absolute_path_for_file_path(relative_file_path);
        let new_content = match sandbox::read_file(&self.app_config.base_dir, &file_path) {
            Ok(content) => content,
            Err(e) => {
                if e.downcast_ref::<std::io::Error>()
                    .is_some_and(|error| error.kind() == std::io::ErrorKind::NotFound)
                {
                    self.file_removed(relative_file_path);
                    return;
                }
                warn!(
                    "The file watcher noticed a file creation/change for {relative_file_path}, \
                    but we couldn't read it: {e} (probably it was deleted after the change?)"
                );
                return;
            }
        };
        self.merge_disk_content(relative_file_path, new_content);
    }

    fn merge_disk_content(&mut self, relative_file_path: &RelativePath, new_content: Vec<u8>) {
        if self.disk_content.get(relative_file_path) == Some(&new_content) {
            return;
        }
        if let Ok(new_content) = String::from_utf8(new_content.clone()) {
            if matches!(
                self.current_file_content(relative_file_path),
                Some(document::Content::String(current)) if *current == new_content
            ) {
                // The outside write is exactly the shared text (for example Git applied the same
                // change a peer made). Merging it would apply that change a second time.
                self.disk_content
                    .insert(relative_file_path.clone(), new_content.into_bytes());
                return;
            }
            let desired = if let (Some(base), Some(document::Content::String(current))) = (
                self.disk_content
                    .get(relative_file_path)
                    .and_then(|bytes| std::str::from_utf8(bytes).ok()),
                self.current_file_content(relative_file_path),
            ) {
                let shared: operational_transform::OperationSeq =
                    TextDelta::from(dissimilar::diff(base, current)).into();
                let outside: operational_transform::OperationSeq =
                    TextDelta::from(dissimilar::diff(base, &new_content)).into();
                let (_, outside) = shared
                    .transform(&outside)
                    .expect("Disk and shared edits have the same base");
                TextDelta::from(outside)
                    .apply_to(current)
                    .expect("Transformed disk edit fits shared text")
            } else {
                new_content.clone()
            };
            self.disk_content
                .insert(relative_file_path.clone(), new_content.into_bytes());
            if let Some(delta) = self.crdt_doc.update_text(&desired, relative_file_path) {
                self.disk_edits.push(ComponentMessage::Edit {
                    file_path: relative_file_path.clone(),
                    delta,
                });
            }
        } else {
            self.invalidate_editor_file(relative_file_path);
            self.disk_content
                .insert(relative_file_path.clone(), new_content.clone());
            self.crdt_doc
                .set_file(document::Content::Bytes(new_content), relative_file_path);
        }
        let _ = self.doc_changed_ping_tx.send(());
    }

    /// Binary replacements invalidate text operations until the editor reopens the file.
    fn invalidate_editor_file(&mut self, path: &RelativePath) {
        for (connection, _) in self.editor_connections.values_mut() {
            connection.invalidate_file(path);
        }
    }

    async fn send_disk_edits(&mut self) {
        // Dropping an editor whose send failed releases files, which can merge another outside
        // write and queue more edits; leaving them queued would let a later broadcast overtake them.
        while !self.disk_edits.is_empty() {
            for message in std::mem::take(&mut self.disk_edits) {
                self.broadcast_to_editors(None, &message).await;
            }
        }
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
    // 🧑 "their save just tells teamtype to write"
    /// Merges outside changes before writing shared text.
    fn write_file(&mut self, file_path: &RelativePath) {
        if self.git_running {
            self.deferred_writes.insert(file_path.clone());
            return;
        }
        if let Err(error) = self.try_write_file(file_path) {
            error!("Could not write shared file {file_path}: {error:#}");
        }
    }

    fn try_write_file(&mut self, file_path: &RelativePath) -> Result<()> {
        if self.git_running {
            self.deferred_writes.insert(file_path.clone());
            anyhow::bail!("Git is running; retry saving when the command finishes");
        }
        let result = self.write_file_now(file_path);
        if result.is_err() {
            // Keep the shared file: a rescan must not read it as deleted on disk, and the next
            // rescan (any watcher event) writes it again.
            self.deferred_writes.insert(file_path.clone());
        }
        result
    }

    fn write_file_now(&mut self, file_path: &RelativePath) -> Result<()> {
        if self.disk_content.contains_key(file_path) {
            self.file_created_or_changed(file_path);
        }
        while let Some(content) = self.current_file_content(file_path).cloned() {
            let bytes = match &content {
                document::Content::String(text) => text.as_bytes(),
                document::Content::Bytes(bytes) => bytes,
            };
            self.ensure_file_has_bytes(file_path, bytes)?;
            if self.current_file_content(file_path) == Some(&content) {
                break;
            }
        }
        self.unmark_pending(file_path);
        Ok(())
    }

    fn ensure_file_has_bytes(&mut self, file_path: &RelativePath, bytes: &[u8]) -> Result<()> {
        if git_forward::excluded(file_path) {
            return Ok(());
        }
        let abs_path = self.absolute_path_for_file_path(file_path);
        if sandbox::exists(&self.app_config.base_dir, &abs_path)
            .context("Failed to check for file existence before writing")?
        {
            if let Ok(current_bytes) = sandbox::read_file(&self.app_config.base_dir, &abs_path) {
                if bytes == current_bytes {
                    debug!("File content is already the desired one, not writing.");
                    // Record what is on disk. A stale record would make the next watcher event
                    // merge this very text as an outside edit, duplicating it.
                    self.disk_content.insert(file_path.clone(), bytes.to_vec());
                    // The record is cleared next; a restart must find the document at least as
                    // new as this file.
                    if self.persist {
                        self.persist()?;
                    }
                    return Ok(());
                }
            } else {
                debug!("Failed to read {abs_path} to check for equal content before writing.");
            }
        } else {
            info!("Creating file {file_path}.");
        }

        if self.persist {
            self.persist()?;
        }
        // The displaced file stays in `.teamtypev` until the document holds its bytes on disk,
        // so a kill right after the swap cannot lose an outside write made since our last read.
        let prefix = self.persist.then(|| displaced_prefix(file_path));
        let (displaced, kept) = sandbox::replace_file_keeping(
            &self.app_config.base_dir,
            &abs_path,
            bytes,
            prefix.as_deref(),
        )
        .with_context(|| format!("Failed to write to file {abs_path}"))?;
        if let Some(displaced) = displaced {
            let outside = self.disk_content.get(file_path) != Some(&displaced);
            // Also without a record: a file created outside and not yet seen by the watcher
            // would otherwise be lost, since its watcher event only finds our bytes. An empty
            // file without a record holds nothing to lose (it may be the placeholder that
            // opening a new file creates), and merging it would replace the shared text.
            if outside && (self.disk_content.contains_key(file_path) || !displaced.is_empty()) {
                self.merge_disk_content(file_path, displaced);
            }
            if outside && self.persist {
                self.displaced_unsaved.extend(kept);
                self.persist()?;
                self.disk_content.insert(file_path.clone(), bytes.to_vec());
                return Ok(());
            }
        }
        if let Some(kept) = kept {
            let _ = std::fs::remove_file(kept);
        }
        self.disk_content.insert(file_path.clone(), bytes.to_vec());
        Ok(())
    }

    /// Removes displaced files that hold the bytes the document itself had: a kill before the
    /// swap left the staged new bytes behind. Must run before anything changes the document.
    fn drop_staged_displaced(&self) {
        let Ok(entries) = std::fs::read_dir(self.app_config.base_dir.join(".teamtypev")) else {
            return;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let Some(path) = name
                .strip_prefix("displaced-")
                .and_then(|rest| rest.split('-').next())
                .and_then(unhex)
            else {
                continue;
            };
            let shared = self
                .current_file_content(&RelativePath::new(&path))
                .map(|content| match content {
                    document::Content::String(text) => text.as_bytes().to_vec(),
                    document::Content::Bytes(bytes) => bytes.clone(),
                });
            if std::fs::read(entry.path()).ok() == shared {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }

    /// After a restart, merges outside writes that a kill displaced from a file while the daemon
    /// was replacing it. `pending_before` is the pending record as the previous run left it; its
    /// base is the common ancestor. Without a base the bytes are kept apart, never dropped.
    fn recover_displaced(&mut self, pending_before: &HashMap<RelativePath, Option<Vec<u8>>>) {
        let dir = self.app_config.base_dir.join(".teamtypev");
        let Ok(entries) = std::fs::read_dir(&dir) else {
            return;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let Some(rest) = name.strip_prefix("displaced-") else {
                continue;
            };
            let Some(path) = rest.split('-').next().and_then(unhex) else {
                continue;
            };
            let path = RelativePath::new(&path);
            let Ok(bytes) = std::fs::read(entry.path()) else {
                continue;
            };
            let on_disk = sandbox::read_file(
                &self.app_config.base_dir,
                &self.absolute_path_for_file_path(&path),
            )
            .ok();
            let shared = self
                .current_file_content(&path)
                .map(|content| match content {
                    document::Content::String(text) => text.as_bytes().to_vec(),
                    document::Content::Bytes(bytes) => bytes.clone(),
                });
            // Equal to what we were writing (killed before the swap) or already merged.
            if shared.as_ref() == Some(&bytes) || on_disk.as_ref() == Some(&bytes) {
                let _ = std::fs::remove_file(entry.path());
                continue;
            }
            if let (Some(base), true, Some(on_disk)) =
                (pending_before.get(&path), shared.is_some(), on_disk)
            {
                {
                    self.disk_content
                        .insert(path.clone(), base.clone().unwrap_or_default());
                    self.merge_disk_content(&path, bytes);
                    self.disk_content.insert(path.clone(), on_disk);
                    // Removed once a save of the document includes the merge.
                    self.displaced_unsaved.push(entry.path());
                    if let Err(error) = self.try_write_file(&path) {
                        warn!("Could not write {path} after merging a displaced edit: {error:#}");
                    }
                }
            } else {
                {
                    let kept = dir.join(format!("lost-{name}"));
                    let _ = std::fs::rename(entry.path(), &kept);
                    warn!(
                        "{path} was replaced while another program changed it; the other \
                         version is kept at {}",
                        kept.display()
                    );
                }
            }
        }
    }

    fn read_current_content_from_dir(&mut self, init: bool) {
        if self.git_running {
            return;
        }
        debug!("Reading current contents from disk (init: {init}).");
        let mut paths = sandbox::enumerate_non_ignored_files(&self.app_config);
        paths.extend(
            self.crdt_doc
                .files()
                .iter()
                .filter(|path| !git_forward::excluded(path))
                .map(|path| self.absolute_path_for_file_path(path).to_path_buf()),
        );
        paths.sort();
        paths.dedup();
        for file_path in paths {
            match sandbox::read_file(&self.app_config.base_dir, &file_path) {
                Ok(bytes) => {
                    let relative_file_path =
                        RelativePath::try_from_path(&self.app_config.base_dir, &file_path)
                            .expect("Walked file path should be within base directory");
                    if git_forward::excluded(&relative_file_path) {
                        continue;
                    }
                    if init {
                        self.disk_content
                            .insert(relative_file_path.clone(), bytes.clone());
                        if let Ok(text) = String::from_utf8(bytes.clone()) {
                            self.crdt_doc
                                .set_file(document::Content::String(text), &relative_file_path);
                        } else {
                            self.crdt_doc
                                .set_file(document::Content::Bytes(bytes), &relative_file_path);
                        }
                    } else {
                        self.file_created_or_changed(&relative_file_path);
                    }
                }
                Err(e) => {
                    warn!("Failed to read file '{}': {e}", file_path.display());
                }
            }
        }

        for relative_file_path in self.crdt_doc.files() {
            if self.deferred_writes.contains(&relative_file_path)
                && !self.disk_content.contains_key(&relative_file_path)
            {
                continue;
            }
            let absolute_file_path = self.absolute_path_for_file_path(&relative_file_path);
            if git_forward::excluded(&relative_file_path) {
                continue;
            }
            if !sandbox::exists(&self.app_config.base_dir, &absolute_file_path).unwrap_or(true) {
                warn!(
                    "File {relative_file_path} exists in the CRDT, but not on disk. Deleting from CRDT."
                );
                self.remove_file(&relative_file_path);
            }
        }
        let _ = self.doc_changed_ping_tx.send(());
    }

    /// Reconciles open files before Git reads them.
    fn flush_git_files(&mut self) -> Result<()> {
        let paths: Vec<_> = self.files_open_in_editors.iter().cloned().collect();
        for path in paths {
            if git_forward::excluded(&path) {
                continue;
            }
            self.try_write_file(&path)?;
        }
        Ok(())
    }

    /// Defers shared-file I/O at the same actor boundary that flushes pre-command edits.
    fn start_git(&mut self, heads: &[ChangeHash]) -> Result<bool> {
        if self.git_running || !self.crdt_doc.has_changes(heads) {
            return Ok(false);
        }
        self.flush_git_files()?;
        self.git_running = true;
        Ok(true)
    }

    /// Merges completed Git writes before writing edits received during the command.
    fn finish_git(&mut self) -> Result<()> {
        if !self.git_running {
            return Ok(());
        }
        self.git_running = false;
        for path in std::mem::take(&mut self.deferred_removals) {
            if !self.crdt_doc.file_exists(&path) {
                self.remove_disk_file(&path);
            }
        }
        self.read_current_content_from_dir(false);
        let mut result = Ok(());
        for path in std::mem::take(&mut self.deferred_writes) {
            if let Err(error) = self.try_write_file(&path) {
                result = Err(error);
            }
        }
        self.flush_git_files()?;
        result
    }

    /// The disk bytes, if they differ from what the daemon last saw there.
    fn unhandled_outside_write(&self, file_path: &RelativePath) -> Option<Vec<u8>> {
        let absolute = self.absolute_path_for_file_path(file_path);
        let bytes = sandbox::read_file(&self.app_config.base_dir, &absolute).ok()?;
        (self.disk_content.get(file_path) != Some(&bytes)).then_some(bytes)
    }

    fn remove_disk_file(&mut self, file_path: &RelativePath) {
        // The disk no longer has the file, so it must not be compared against later; otherwise
        // the next write of a recreated file reads the missing file as a local deletion.
        self.disk_content.remove(file_path);
        let absolute = self.absolute_path_for_file_path(file_path);
        if let Err(error) = sandbox::remove_file(&self.app_config.base_dir, &absolute) {
            warn!("Failed to remove file {file_path}: {error}");
        }
        if !matches!(
            sandbox::exists(&self.app_config.base_dir, &absolute),
            Ok(true)
        ) {
            self.unmark_pending(file_path);
        }
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
            self.disk_content.remove(file_path);
        } else {
            self.merge_disk_content(file_path, vec![]);
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
        loop {
            // Writes that failed or were deferred are retried on every rescan; with no further
            // file events, nothing would trigger one, so also retry on a timer.
            let retry_pending = !self.deferred_writes.is_empty() && !self.git_running;
            tokio::select! {
                message = self.doc_message_rx.recv() => {
                    let Some(message) = message else { break };
                    self.handle_message(message).await;
                }
                () = sleep(WRITE_RETRY_INTERVAL), if retry_pending => {
                    self.handle_message(DocMessage::RescanFiles).await;
                }
            }
        }
        debug!("Channel towards document handle has been closed (probably shutting down).");
    }
}

#[cfg(not(test))]
const WRITE_RETRY_INTERVAL: Duration = Duration::from_secs(5);
#[cfg(test)]
const WRITE_RETRY_INTERVAL: Duration = Duration::from_millis(50);

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
    pub git: git_forward::GitHandle,
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

        let git = git_forward::GitHandle::new();
        tokio::spawn(async move { actor.run().await });

        Self {
            doc_message_tx,
            doc_changed_ping_tx,
            ephemeral_message_tx,
            git,
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

    pub async fn git_heads(&self) -> Vec<ChangeHash> {
        let (response_tx, response_rx) = oneshot::channel();
        self.send_message(DocMessage::GitHeads { response_tx })
            .await;
        response_rx.await.unwrap_or_default()
    }

    pub async fn git_ready(&self, heads: Vec<ChangeHash>) -> Result<bool> {
        let (response_tx, response_rx) = oneshot::channel();
        self.send_message(DocMessage::GitReady { heads, response_tx })
            .await;
        response_rx
            .await
            .unwrap_or_else(|_| Err(anyhow::anyhow!("Document actor stopped")))
    }

    pub async fn git_started(&self, heads: Vec<ChangeHash>) -> Result<bool> {
        let (response_tx, response_rx) = oneshot::channel();
        self.send_message(DocMessage::GitStarted { heads, response_tx })
            .await;
        response_rx
            .await
            .unwrap_or_else(|_| Err(anyhow::anyhow!("Document actor stopped")))
    }

    pub async fn git_finished(&self) -> Result<()> {
        let (response_tx, response_rx) = oneshot::channel();
        self.send_message(DocMessage::GitFinished { response_tx })
            .await;
        response_rx
            .await
            .unwrap_or_else(|_| Err(anyhow::anyhow!("Document actor stopped")))
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

        git_forward::start(document_handle.clone())?;

        // Start file watcher.
        spawn_file_watcher(&app_config, document_handle.clone());

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
                    /// Others can connect by putting the following secret address in their .teamtypev/config:
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
                        "The sharer runs a teamtypev version that cannot sync with yours; install the same build on both sides",
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
                        if watcher_event.file_path.strip_prefix(document_handle.base_dir())
                            .is_ok_and(git_forward::excluded) {
                            continue;
                        }
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

/// File name prefix of a displaced file kept while `path` is replaced.
fn displaced_prefix(path: &RelativePath) -> String {
    use std::fmt::Write;
    let hex = path
        .display()
        .to_string()
        .bytes()
        .fold(String::new(), |mut hex, byte| {
            let _ = write!(hex, "{byte:02x}");
            hex
        });
    format!("displaced-{hex}-")
}

fn unhex(hex: &str) -> Option<String> {
    let bytes: Option<Vec<u8>> = (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(hex.get(i..i + 2)?, 16).ok())
        .collect();
    String::from_utf8(bytes?).ok()
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
        include!("daemon_save_tests.rs");
        use tempfile::{TempDir, tempdir};

        use super::*;

        #[expect(clippy::unused_async, clippy::match_same_arms)]
        mod races {
            use tempfile::{TempDir, tempdir};

            use super::*;
            include!("daemon_race_tests.rs");
        }
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

        fn restart(dir: &TempDir) -> DocumentActor {
            let (_tx, rx) = mpsc::channel(1);
            let (ping, _ping_rx) = broadcast::channel::<()>(1);
            let (eph, _eph_rx) = broadcast::channel::<EphemeralMessage>(100);
            DocumentActor::new(
                rx,
                ping,
                eph,
                AppConfig {
                    base_dir: dir.path().to_path_buf(),
                    ..Default::default()
                },
                false,
                true,
                true,
            )
        }

        /// A crash after a peer's edit was saved in the document but before it reached the file
        /// (for example while Git ran and the write was deferred) must not revert that edit.
        #[tokio::test]
        async fn restart_keeps_saved_edits_not_yet_on_disk() {
            let dir = setup_filesystem_for_testing();
            let mut actor = restart(&dir);
            let file1 = RelativePath::new("file1");
            let new_file = RelativePath::new("peer-new");
            // A peer's sync message arrives while Git runs, so the write is deferred; the
            // document is saved; then the daemon dies.
            actor.git_running = true;
            let mut peer = Document::load(&actor.crdt_doc.save());
            let _ = peer.update_text("content1 plus peer", &file1);
            peer.set_file(document::Content::String("fresh".into()), &new_file);
            let mut peer_state = SyncState::new();
            let mut own_state = SyncState::new();
            for _ in 0..6 {
                if let Some(message) = peer.generate_sync_message(&mut peer_state) {
                    let (tx, rx) = oneshot::channel();
                    actor
                        .handle_message(DocMessage::ReceiveSyncMessage {
                            message,
                            state: own_state,
                            response_tx: tx,
                        })
                        .await;
                    own_state = rx.await.unwrap();
                }
                if let Some(message) = actor.crdt_doc.generate_sync_message(&mut own_state) {
                    let _ = peer.receive_sync_message_log_patches(message, &mut peer_state);
                }
            }
            assert!(actor.crdt_doc.file_exists(&new_file));
            actor.persist().unwrap();
            drop(actor);
            // Git changed another file and a different line meanwhile.
            std::fs::write(dir.path().join("file2"), "git made this").unwrap();
            std::fs::write(dir.path().join("file1"), "local content1").unwrap();

            let actor = restart(&dir);
            actor.assert_file_content(&RelativePath::new("file2"), "git made this");
            actor.assert_file_content(&new_file, "fresh");
        }

        #[test]
        fn hostile_peer_paths_do_not_crash_rescan_or_escape() {
            let dir = setup_filesystem_for_testing();
            let mut actor = DocumentActor::setup_for_testing(&dir);
            for key in [
                "../escape-by-dotdot",
                "/tmp/tt-escape-abs",
                "a/../../escape2",
            ] {
                actor.crdt_doc.set_file(
                    document::Content::String("x".into()),
                    &RelativePath::new(key),
                );
            }
            actor.read_current_content_from_dir(false);
            for key in [
                "../escape-by-dotdot",
                "/tmp/tt-escape-abs",
                "a/../../escape2",
            ] {
                actor.write_file(&RelativePath::new(key));
            }
            assert!(
                !dir.path()
                    .parent()
                    .unwrap()
                    .join("escape-by-dotdot")
                    .exists()
            );
            assert!(!Path::new("/tmp/tt-escape-abs").exists());
        }

        #[tokio::test]
        async fn edits_queued_while_dropping_a_dead_editor_are_still_sent() {
            let dir = setup_filesystem_for_testing();
            let mut actor = DocumentActor::setup_for_testing(&dir);
            let path = RelativePath::new("file1");
            let uri = actor
                .absolute_path_for_file_path(&path)
                .to_file_uri()
                .to_string();
            let mut readers = vec![];
            for id in [1, 2] {
                let (stream, reader) = tokio::net::UnixStream::pair().expect("editor socket");
                let (_, writer) = tokio::io::split(stream);
                readers.push(reader);
                actor.editor_connections.insert(
                    id,
                    (
                        EditorConnection::new("test".into(), actor.app_config.clone()),
                        tokio_util::codec::FramedWrite::new(writer, editor::OutgoingProtocolCodec),
                    ),
                );
                actor
                    .react_to_message_from_editor(
                        id,
                        &EditorProtocolMessageFromEditor::Open {
                            uri: uri.clone(),
                            content: "content1".into(),
                            saves_file: false,
                            daemon_writes: true,
                        },
                    )
                    .await
                    .expect("open");
            }
            // Editor 1 disconnects; a write is merged, and another lands before the broadcast.
            drop(readers.remove(0));
            std::fs::write(dir.path().join("file1"), "first outside write").expect("write");
            actor.file_created_or_changed(&path);
            std::fs::write(dir.path().join("file1"), "second outside write, longer")
                .expect("write");
            actor.send_disk_edits().await;
            assert_eq!(actor.disk_edits.len(), 0, "edits stayed queued");
            let Some(document::Content::String(shared)) = actor.current_file_content(&path) else {
                panic!("shared text")
            };
            assert_eq!(
                actor.editor_connections[&2].0.server_text(&path),
                Some(shared.as_str())
            );
        }

        /// The failure the queue leak caused: a peer's sync delta, relative to a text that includes
        /// the leaked edit, reached an editor that had not been told the edit, and its OT server
        /// panicked in `message_from_inside`.
        #[tokio::test]
        async fn sync_delta_does_not_overtake_edits_left_by_a_dead_editor() {
            let dir = setup_filesystem_for_testing();
            let mut actor = DocumentActor::setup_for_testing(&dir);
            let path = RelativePath::new("file1");
            let uri = actor
                .absolute_path_for_file_path(&path)
                .to_file_uri()
                .to_string();
            let mut readers = vec![];
            for id in [1, 2] {
                let (stream, reader) = tokio::net::UnixStream::pair().expect("editor socket");
                let (_, writer) = tokio::io::split(stream);
                readers.push(reader);
                actor.editor_connections.insert(
                    id,
                    (
                        EditorConnection::new("test".into(), actor.app_config.clone()),
                        tokio_util::codec::FramedWrite::new(writer, editor::OutgoingProtocolCodec),
                    ),
                );
                actor
                    .react_to_message_from_editor(
                        id,
                        &EditorProtocolMessageFromEditor::Open {
                            uri: uri.clone(),
                            content: "content1".into(),
                            saves_file: false,
                            daemon_writes: true,
                        },
                    )
                    .await
                    .expect("open");
            }
            // A peer with the same history; finish the sync handshake so one message carries a change.
            let mut peer = Document::load(&actor.crdt_doc.save());
            let mut peer_state = SyncState::new();
            let mut actor_state = SyncState::new();
            for _ in 0..6 {
                if let Some(message) = peer.generate_sync_message(&mut peer_state) {
                    let (tx, rx) = oneshot::channel();
                    actor
                        .handle_message(DocMessage::ReceiveSyncMessage {
                            message,
                            state: std::mem::replace(&mut actor_state, SyncState::new()),
                            response_tx: tx,
                        })
                        .await;
                    actor_state = rx.await.expect("state");
                }
                let (tx, rx) = oneshot::channel();
                actor
                    .handle_message(DocMessage::GenerateSyncMessage {
                        state: std::mem::replace(&mut actor_state, SyncState::new()),
                        response_tx: tx,
                    })
                    .await;
                let (state, message) = rx.await.expect("state");
                actor_state = state;
                if let Some(message) = message {
                    let _ = peer.receive_sync_message_log_patches(message, &mut peer_state);
                }
            }
            // Editor 1 disconnects; two outside writes are merged while its removal is handled.
            drop(readers.remove(0));
            std::fs::write(dir.path().join("file1"), "first outside write").expect("write");
            actor.file_created_or_changed(&path);
            std::fs::write(
                dir.path().join("file1"),
                "second outside write, much longer",
            )
            .expect("write");
            actor.send_disk_edits().await;
            // The peer edits the end of the text it knows; its delta is based on the merged text.
            peer.update_text("content1 and the peer's tail", &path);
            let message = peer
                .generate_sync_message(&mut peer_state)
                .expect("sync message with the peer's edit");
            let (tx, rx) = oneshot::channel();
            actor
                .handle_message(DocMessage::ReceiveSyncMessage {
                    message,
                    state: actor_state,
                    response_tx: tx,
                })
                .await;
            let _ = rx.await;
            assert_eq!(actor.disk_edits.len(), 0);
            let Some(document::Content::String(shared)) = actor.current_file_content(&path) else {
                panic!("shared text")
            };
            assert_eq!(
                actor.editor_connections[&2].0.server_text(&path),
                Some(shared.as_str())
            );
        }

        #[tokio::test]
        async fn outside_write_is_merged_before_saving_an_open_file() {
            let dir = setup_filesystem_for_testing();
            let mut actor = DocumentActor::setup_for_testing(&dir);
            let path = RelativePath::new("file1");
            let uri = actor
                .absolute_path_for_file_path(&path)
                .to_file_uri()
                .to_string();
            let (stream, _reader) = tokio::net::UnixStream::pair().expect("editor socket");
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
            for n in 0..20 {
                let old = match actor.current_file_content(&path) {
                    Some(document::Content::String(text)) => text.clone(),
                    _ => panic!("shared text"),
                };
                let outside = format!("{old}\noutside-{n}");
                std::fs::write(dir.path().join("file1"), &outside).expect("outside write");
                let shared = format!("typed-{n}\n{old}");
                let delta = TextDelta::from(dissimilar::diff(&old, &shared));
                let (message, _) = actor
                    .editor_connections
                    .get_mut(&1)
                    .expect("editor")
                    .0
                    .message_from_editor(
                        true,
                        &EditorProtocolMessageFromEditor::Edit {
                            uri: uri.clone(),
                            revision: n,
                            delta: crate::types::EditorTextDelta::try_from_delta(delta, &old)
                                .expect("editor delta"),
                        },
                    )
                    .expect("local edit before watcher delivery");
                let ComponentMessage::Edit { delta, .. } = message else {
                    panic!("edit")
                };
                actor
                    .crdt_doc
                    .apply_delta_to_doc(&delta, &path)
                    .expect("typing before watcher delivery");
                if n % 2 == 0 {
                    actor.flush_git_files().expect("Git flush");
                    actor.send_disk_edits().await;
                } else {
                    actor
                        .react_to_message_from_editor(
                            1,
                            &EditorProtocolMessageFromEditor::Save { uri: uri.clone() },
                        )
                        .await
                        .expect("save");
                }
                let expected = format!("typed-{n}\n{outside}");
                actor.assert_file_content(&path, &expected);
                assert_eq!(
                    std::fs::read_to_string(dir.path().join("file1")).expect("disk"),
                    expected
                );
            }
            std::fs::write(dir.path().join("file1"), [0xff]).expect("outside binary write");
            for message in [
                EditorProtocolMessageFromEditor::Save { uri: uri.clone() },
                EditorProtocolMessageFromEditor::Edit {
                    uri,
                    revision: 20,
                    delta: crate::types::EditorTextDelta(vec![]),
                },
            ] {
                assert!(
                    actor
                        .react_to_message_from_editor(1, &message)
                        .await
                        .is_err()
                );
                assert_eq!(
                    std::fs::read(dir.path().join("file1")).expect("binary"),
                    [0xff]
                );
            }
            actor
                .react_to_message_from_editor(1, &EditorProtocolMessageFromEditor::DaemonWriter {})
                .await
                .expect("actor remains alive");
        }
    }
}
