// SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::mem;

use anyhow::{Context, Result, bail};
use async_trait::async_trait;
use automerge::sync::{Message as AutomergeSyncMessage, State as AutomergeSyncState};
use serde::{Deserialize, Serialize};
use tokio::sync::{broadcast::error::RecvError, oneshot};
use tracing::{debug, warn};

use crate::daemon::{DocMessage, DocumentActorHandle};
use crate::types::EphemeralMessage;
use crate::vcs_files::VcsMessage;

#[derive(Deserialize, Serialize)]
/// The `PeerMessage` is used for peer to peer data exchange.
pub enum PeerMessage {
    /// The Sync message contains the changes to the CRDT
    Sync(Vec<u8>),
    /// The Ephemeral message currently is used for cursor messages, but can later be used for
    /// other things that should not be persisted.
    Ephemeral(EphemeralMessage),
    /// Version-control files, which are not in the CRDT; see `vcs_files`.
    Vcs(VcsMessage),
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
}

impl SyncActor {
    pub fn new(
        document_handle: DocumentActorHandle,
        connection: Box<dyn Connection<PeerMessage>>,
    ) -> Self {
        Self {
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
            PeerMessage::Vcs(message) => {
                self.document_handle
                    .send_message(DocMessage::ReceiveVcs(message))
                    .await;
            }
        }
        Ok(())
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
        // Subscribed before taking the snapshot, so that no change is missed.
        let mut vcs_messages_rx = self.document_handle.subscribe_vcs_messages();

        // Kick off initial synchronization with peer.
        self.generate_sync_message().await?;
        for message in self.document_handle.vcs_snapshot().await {
            self.connection.send(PeerMessage::Vcs(message)).await?;
        }

        loop {
            tokio::select! {
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
                vcs_message = vcs_messages_rx.recv() => {
                    match vcs_message {
                        Ok(message) => self.connection.send(PeerMessage::Vcs(message)).await?,
                        Err(RecvError::Closed) => panic!("Version-control channel has been closed"),
                        Err(RecvError::Lagged(n)) => {
                            warn!("Missed {n} version-control changes for a peer; it reconnects to resync.");
                            bail!("Version-control channel lagged");
                        }
                    }
                }
                message = self.connection.next() => {
                    self.receive_peer_message(message?).await?;
                }
            }
        }
    }
}
