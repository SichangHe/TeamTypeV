// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

//! This module provides a [`ConnectionManager`], which can be used to connect to other daemons.

use std::collections::HashMap;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::Path;
use std::str::FromStr;
use std::time::Duration;

use anyhow::bail;
use anyhow::{Context, Result};
use async_trait::async_trait;
use iroh::address_lookup::DnsAddressLookup;
use iroh::address_lookup::pkarr::PkarrPublisher;
use iroh::endpoint::{
    Connection as IrohEndpointConnection, RecvStream, RelayMode, SendStream, presets,
};
use iroh::{Endpoint, EndpointAddr, PublicKey, RelayMap, RelayUrl, SecretKey};
use postcard::{from_bytes, to_allocvec};
use tokio::sync::{mpsc, oneshot};
use tokio::task::JoinHandle;
use tokio::time::{sleep, timeout};
use tracing::{debug, info, warn};
use url::Url;

use self::sync::{Connection, PeerMessage, SyncActor};
use crate::config::AppConfig;
use crate::daemon::DocumentActorHandle;

mod sync;
mod tunnel;

pub use tunnel::run as run_tunnel;

/// Changes whenever peers of different versions cannot understand each other, so that they fail
/// to connect with a clear message instead of disconnecting after every message.
const ALPN: &[u8] = b"/teamtype-fork/2";

const PEER_TIMEOUT: Duration = Duration::from_secs(6);

struct SecretAddress {
    endpoint_addr: EndpointAddr,
    passphrase: SecretKey,
}

impl FromStr for SecretAddress {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        let parts: Vec<&str> = s.split('#').collect();
        if parts.len() != 2 {
            bail!("Peer string must have format <endpoint_id>#<passphrase>");
        }

        let endpoint_addr = PublicKey::from_str(parts[0])?.into();
        let passphrase = SecretKey::from_str(parts[1])?;

        Ok(Self {
            endpoint_addr,
            passphrase,
        })
    }
}

enum PeerAuth {
    MyPassphrase(SecretKey),
    YourPassphrase(SecretKey),
}

pub struct ConnectionManager {
    message_tx: mpsc::Sender<EndpointMessage>,
    secret_address: String,
}

impl ConnectionManager {
    pub async fn new(
        app_config: &AppConfig,
        document_handle: DocumentActorHandle,
        base_dir: &Path,
    ) -> Result<Self> {
        let (message_tx, message_rx) = mpsc::channel(1);

        let (endpoint, my_passphrase) = Self::build_endpoint(app_config, base_dir).await?;

        let encoded_passphrase = data_encoding::HEXLOWER.encode(&my_passphrase.to_bytes());
        let secret_address = format!("{}#{}", endpoint.id(), encoded_passphrase);

        let mut actor = EndpointActor::new(
            endpoint,
            message_rx,
            message_tx.clone(),
            document_handle,
            my_passphrase,
            app_config.clone(),
        );
        actor.forward_port = app_config.forward_port;

        tokio::spawn(async move { actor.run().await });

        Ok(Self {
            message_tx,
            secret_address,
        })
    }

    #[must_use]
    pub fn secret_address(&self) -> &str {
        &self.secret_address
    }

    pub async fn connect(&self, secret_address: String) -> Result<()> {
        let (response_tx, response_rx) = oneshot::channel();

        self.message_tx
            .send(EndpointMessage::Connect {
                secret_address: SecretAddress::from_str(&secret_address)?,
                response_tx: Some(response_tx),
                previous_attempts: 0,
                generation: None,
            })
            .await
            .expect("EndpointActor task has been killed");

        response_rx.await??;

        Ok(())
    }

    async fn build_endpoint(
        app_config: &AppConfig,
        base_dir: &Path,
    ) -> Result<(Endpoint, SecretKey)> {
        if !app_config.is_host() {
            Self::forget_copied_key(base_dir);
        }
        let (secret_key, my_passphrase) = Self::get_keypair(base_dir);
        Ok((
            Self::bind_endpoint(app_config, secret_key).await?,
            my_passphrase,
        ))
    }

    /// Binds an endpoint without reading or changing the daemon's identity on disk.
    async fn bind_endpoint(app_config: &AppConfig, secret_key: SecretKey) -> Result<Endpoint> {
        let mut builder = Endpoint::builder(presets::N0)
            .secret_key(secret_key)
            .alpns(vec![ALPN.to_vec(), tunnel::ALPN.to_vec()]);

        let relay_mode = match &app_config.iroh_relay {
            Some(iroh_relay) => {
                let relay_url = RelayUrl::from_str(iroh_relay)?;
                let relay_map = RelayMap::from(relay_url);
                RelayMode::Custom(relay_map)
            }
            _ => RelayMode::Default,
        };
        builder = builder.relay_mode(relay_mode);

        let iroh_dns_lookup = app_config.iroh_dns_domain.as_ref().map_or_else(
            DnsAddressLookup::n0_dns,
            |iroh_dns_domain| {
                let iroh_dns_domain_clone = iroh_dns_domain.clone();
                DnsAddressLookup::builder(iroh_dns_domain_clone)
            },
        );
        builder = builder.address_lookup(iroh_dns_lookup);

        let iroh_pkarr_lookup = match &app_config.iroh_pkarr_relay {
            Some(iroh_pkarr_relay) => {
                let iroh_pkarr_relay_url = Url::parse(iroh_pkarr_relay)?;
                PkarrPublisher::builder(iroh_pkarr_relay_url)
            }
            _ => PkarrPublisher::n0_dns(),
        };
        builder = builder.address_lookup(iroh_pkarr_lookup);

        Ok(builder.bind().await?)
    }

    /// A joiner whose `.teamtype` was copied from another directory would share that directory's
    /// identity, and the two would keep replacing each other's connection. So a joiner's key is
    /// tied to its directory, and a copied one is replaced.
    fn forget_copied_key(base_dir: &Path) {
        let teamtype_dir = base_dir.join(".teamtype");
        let key_dir_file = teamtype_dir.join("key-dir");
        let this_dir = fs::canonicalize(base_dir).unwrap_or_else(|_| base_dir.to_path_buf());
        let this_dir = this_dir.display().to_string();
        let key_dir = fs::read_to_string(&key_dir_file).ok();
        if key_dir.as_deref() != Some(this_dir.as_str()) {
            if teamtype_dir.join("key").exists() {
                info!("This directory's .teamtype/key was made elsewhere; making a new one.");
                let _ = fs::remove_file(teamtype_dir.join("key"));
            }
            if let Err(err) = fs::write(&key_dir_file, &this_dir) {
                warn!("Failed to write {}: {err}", key_dir_file.display());
            }
        }
    }

    fn get_keypair(base_dir: &Path) -> (SecretKey, SecretKey) {
        let keyfile = base_dir.join(".teamtype").join("key");
        if keyfile.exists() {
            let metadata =
                fs::metadata(&keyfile).expect("Expected to have access to metadata of the keyfile");

            let current_permissions = metadata.permissions().mode();
            let allowed_permissions = 0o100_600;
            assert!(
                current_permissions == allowed_permissions,
                "For security reasons, please make sure to set the key file to user-readable only (set the permissions to 600)."
            );

            assert!(
                metadata.len() == 64,
                "Your keyfile is not 64 bytes long. This is a sign that it was created by a Teamtype version older than 0.7.0, which is not compatible. Please remove .teamtype/key, and try again."
            );

            debug!("Re-using existing keypair.");
            let mut file = File::open(keyfile).expect("Failed to open key file");

            let mut secret_key = [0; 32];
            file.read_exact(&mut secret_key)
                .expect("Failed to read from key file");

            let mut passphrase = [0; 32];
            file.read_exact(&mut passphrase)
                .expect("Failed to read from key file");

            (
                SecretKey::from_bytes(&secret_key),
                SecretKey::from_bytes(&passphrase),
            )
        } else {
            debug!("Generating new keypair.");
            let secret_key = SecretKey::generate();
            let passphrase = SecretKey::generate();

            let mut file = OpenOptions::new()
                .create_new(true)
                .write(true)
                .mode(0o600)
                .open(keyfile)
                .expect("Should have been able to create key file that did not exist before");

            file.write_all(&secret_key.to_bytes())
                .expect("Failed to write to key file");
            file.write_all(&passphrase.to_bytes())
                .expect("Failed to write to key file");

            (secret_key, passphrase)
        }
    }
}

enum EndpointMessage {
    // Instruct the endpoint to connect to a new peer.
    Connect {
        // All information we need to connect to another peer.
        secret_address: SecretAddress,
        // On connection success, this channel will be pinged.
        // Used for the initial connection, where we want to fail if connecting fails.
        response_tx: Option<oneshot::Sender<Result<()>>>,
        // How many times have we already attempted to connect?
        previous_attempts: usize,
        // Reconnects from an older connection must not replace a newer one.
        generation: Option<u64>,
    },
}

// Owns the Iroh endpoint, accepts incoming connections, and can be instructed to connect to
// another daemon.
struct EndpointActor {
    endpoint: Endpoint,
    app_config: AppConfig,
    message_rx: mpsc::Receiver<EndpointMessage>,
    message_tx: mpsc::Sender<EndpointMessage>,
    document_handle: DocumentActorHandle,
    my_passphrase: SecretKey,
    peer_tasks: HashMap<PublicKey, JoinHandle<()>>,
    peer_generations: HashMap<PublicKey, u64>,
    next_generation: u64,
    forward_port: Option<u16>,
    /// Recent connection times per peer, to notice two peers that share a key.
    recent_connections: HashMap<PublicKey, Vec<std::time::Instant>>,
}

impl EndpointActor {
    fn new(
        endpoint: Endpoint,
        message_rx: mpsc::Receiver<EndpointMessage>,
        message_tx: mpsc::Sender<EndpointMessage>,
        document_handle: DocumentActorHandle,
        my_passphrase: SecretKey,
        app_config: AppConfig,
    ) -> Self {
        Self {
            endpoint,
            app_config,
            message_rx,
            message_tx,
            document_handle,
            my_passphrase,
            peer_tasks: HashMap::new(),
            peer_generations: HashMap::new(),
            next_generation: 0,
            forward_port: None,
            recent_connections: HashMap::new(),
        }
    }

    async fn handle_message(&mut self, message: EndpointMessage) -> Result<()> {
        match message {
            EndpointMessage::Connect {
                secret_address,
                response_tx,
                previous_attempts,
                generation,
            } => {
                let peer_id = secret_address.endpoint_addr.id;
                if let Some(generation) = generation
                    && self.peer_generations.get(&peer_id) != Some(&generation)
                {
                    debug!("Ignoring stale reconnect attempt for peer {peer_id}.");
                    return Ok(());
                }
                let generation = self.start_peer_generation(peer_id);
                if previous_attempts > 1
                    && !self.app_config.is_host()
                    && self.peer_tasks.values().all(JoinHandle::is_finished)
                {
                    match ConnectionManager::bind_endpoint(
                        &self.app_config,
                        self.endpoint.secret_key().clone(),
                    )
                    .await
                    {
                        Ok(endpoint) => {
                            let previous_endpoint = std::mem::replace(&mut self.endpoint, endpoint);
                            tokio::spawn(async move { previous_endpoint.close().await });
                        }
                        Err(err) => warn!("Could not refresh the disconnected endpoint: {err:#}"),
                    }
                }
                if response_tx.is_none() {
                    self.endpoint.dns_resolver()?.reset();
                    self.endpoint.network_change().await;
                }
                let endpoint_addr = secret_address.endpoint_addr.clone();
                let connect = self.endpoint.connect(endpoint_addr, ALPN);
                let connect_result = if response_tx.is_some() {
                    connect.await.map_err(anyhow::Error::from)
                } else {
                    timeout(Duration::from_secs(8), connect)
                        .await
                        .map_err(anyhow::Error::from)
                        .and_then(|result| result.map_err(anyhow::Error::from))
                };
                let conn = match connect_result {
                    Ok(conn) => conn,
                    Err(err) => {
                        if format!("{err:#}").contains("known protocol") {
                            warn!(
                                "The peer runs a teamtype version that cannot sync with yours; install the same build on both sides."
                            );
                        }
                        if let Some(response_tx) = response_tx {
                            response_tx
                                .send(Err(err))
                                .expect("Connect receiver dropped");
                        }
                        Self::reconnect(
                            self.message_tx.clone(),
                            secret_address,
                            previous_attempts,
                            generation,
                        )
                        .await
                        .expect("Failed to initiate reconnection");
                        // Not really Ok, but Ok enough.
                        return Ok(());
                    }
                };
                if self.peer_generations.get(&peer_id) != Some(&generation) {
                    debug!("Dropping superseded connection to peer {peer_id}.");
                    return Ok(());
                }

                info!(
                    "Connected to peer: {}. Teamtype keeps syncing while it runs; press Ctrl+C to stop.",
                    conn.remote_id()
                );

                if let Some(response_tx) = response_tx {
                    response_tx.send(Ok(())).expect("Connect receiver dropped");
                }

                let peer_id = conn.remote_id();
                let document_handle = self.document_handle.clone();
                let message_tx = self.message_tx.clone();
                let passphrase = secret_address.passphrase.clone();
                let task = tokio::spawn(async move {
                    if let Err(err) = Self::handle_peer(
                        document_handle,
                        conn,
                        PeerAuth::YourPassphrase(passphrase),
                    )
                    .await
                    {
                        debug!("Error while handling a peer: {:?}", err);
                    }
                    Self::reconnect(message_tx, secret_address, 0, generation)
                        .await
                        .expect("Failed to initiate reconnection");
                });
                self.peer_tasks.insert(peer_id, task);
            }
        }
        Ok(())
    }

    /// Two processes with the same `.teamtype/key`, for example in a copied `.teamtype`
    /// directory, keep replacing each other's connection.
    fn warn_if_flapping(&mut self, peer_id: PublicKey) {
        let now = std::time::Instant::now();
        let times = self.recent_connections.entry(peer_id).or_default();
        times.retain(|at| now.duration_since(*at) < Duration::from_mins(1));
        times.push(now);
        if times.len() == 10 {
            warn!(
                "Peer {peer_id} connected 10 times in a minute. Two teamtype processes probably use the same .teamtype/key, for example in a copied .teamtype directory, and keep replacing each other; delete .teamtype/key in all but one."
            );
        }
    }

    fn start_peer_generation(&mut self, peer_id: PublicKey) -> u64 {
        self.next_generation += 1;
        if let Some(previous_task) = self.peer_tasks.remove(&peer_id) {
            previous_task.abort();
            debug!("Replaced an existing connection to peer {peer_id}.");
        }
        self.peer_generations.insert(peer_id, self.next_generation);
        self.next_generation
    }

    async fn reconnect(
        message_tx: mpsc::Sender<EndpointMessage>,
        secret_address: SecretAddress,
        previous_attempts: usize,
        generation: u64,
    ) -> Result<()> {
        static LOSSES: std::sync::Mutex<Vec<std::time::Instant>> =
            std::sync::Mutex::new(Vec::new());
        // Only log at "info" level if this is the first reconnection attempt.
        if previous_attempts == 0 {
            info!(
                "Connection to peer {} lost, will keep trying to reconnect...",
                secret_address.endpoint_addr.id
            );
            if let Ok(mut losses) = LOSSES.lock() {
                let now = std::time::Instant::now();
                losses.retain(|at| now.duration_since(*at) < Duration::from_mins(1));
                losses.push(now);
                if losses.len() == 10 {
                    warn!(
                        "The connection dropped 10 times in a minute. Another teamtype process probably uses this directory's .teamtype/key, for example in a copied .teamtype directory, and keeps replacing this connection; delete .teamtype/key in the copy."
                    );
                }
            }
        } else {
            sleep(Duration::from_secs(1)).await;
            debug!(
                "Making another attempt to connect to peer {}...",
                secret_address.endpoint_addr.id
            );
        }
        // We don't need to be notified, so we don't need to use the response channel.
        message_tx
            .send(EndpointMessage::Connect {
                secret_address,
                response_tx: None,
                previous_attempts: previous_attempts + 1,
                generation: Some(generation),
            })
            .await?;
        Ok(())
    }

    async fn run(&mut self) {
        loop {
            tokio::select! {
                maybe_incoming = self.endpoint.accept() => {
                    match maybe_incoming {
                        Some(incoming) => {
                            match incoming.await {
                                Ok(conn) => {
                                    self.handle_incoming_connection(conn);
                                }
                                Err(err) => {
                                    debug!("Error while accepting peer connection: {err}");
                                }
                            }
                        }
                        None => {
                            // Endpoint was closed. Let's shut down.
                            break
                        }
                    }
                }
                maybe_message = self.message_rx.recv() => {
                    match maybe_message {
                        Some(message) => {
                            self.handle_message(message).await.expect("Failed to handle endpoint message");
                        }
                        None => {
                            // Our message channel was closed? Let's shut down.
                            break
                        }
                    }
                }
            }
        }
    }

    fn handle_incoming_connection(&mut self, conn: IrohEndpointConnection) {
        let endpoint_id = conn.remote_id();
        if conn.alpn() == tunnel::ALPN {
            if let Some(port) = self.forward_port {
                debug!("Tunnel connected: {endpoint_id}");
                tokio::spawn(tunnel::serve(conn, self.my_passphrase.clone(), port));
            }
            return;
        }

        info!("Peer connected: {}", &endpoint_id);
        self.warn_if_flapping(endpoint_id);
        self.start_peer_generation(endpoint_id);

        let my_passphrase = self.my_passphrase.clone();
        let document_handle = self.document_handle.clone();
        let task = tokio::spawn(async move {
            if let Err(err) =
                Self::handle_peer(document_handle, conn, PeerAuth::MyPassphrase(my_passphrase))
                    .await
            {
                warn!("Incoming connection failed: {err}");
            }

            info!("Peer disconnected: {endpoint_id}",);
        });
        self.peer_tasks.insert(endpoint_id, task);
    }

    async fn handle_peer(
        document_handle: DocumentActorHandle,
        conn: IrohEndpointConnection,
        auth: PeerAuth,
    ) -> Result<()> {
        let result = async {
            let stream =
                timeout(PEER_TIMEOUT, PeerMessageStream::new(conn.clone(), auth)).await??;
            let syncer = SyncActor::new(document_handle, Box::new(stream));
            syncer.run().await
        }
        .await;
        conn.close(0u32.into(), b"peer sync ended");
        result
    }
}

// Sends/receives PeerMessages through an Iroh connection.
struct PeerMessageStream {
    message_tx: mpsc::Sender<PeerMessage>,
    message_rx: mpsc::Receiver<Result<PeerMessage>>,
    read_task: JoinHandle<()>,
    write_task: JoinHandle<()>,
}

impl Drop for PeerMessageStream {
    fn drop(&mut self) {
        self.read_task.abort();
        self.write_task.abort();
    }
}

impl PeerMessageStream {
    async fn new(conn: IrohEndpointConnection, auth: PeerAuth) -> Result<Self> {
        let (send, receive) = match auth {
            PeerAuth::YourPassphrase(passphrase) => {
                let (mut send, recv) = conn.open_bi().await?;

                send.write_all(&passphrase.to_bytes()).await?;

                (send, recv)
            }
            PeerAuth::MyPassphrase(passphrase) => {
                let (send, mut recv) = conn.accept_bi().await?;

                let mut received_passphrase = [0; 32];
                recv.read_exact(&mut received_passphrase).await?;

                // Guard against timing attacks.
                if !constant_time_eq::constant_time_eq(&received_passphrase, &passphrase.to_bytes())
                {
                    bail!("Peer provided incorrect passphrase.");
                }

                (send, recv)
            }
        };

        let (message_tx, message_rx) = mpsc::channel(1);
        let read_conn = conn.clone();
        let read_task = tokio::spawn(async move {
            let _ = Self::read_loop(receive, message_tx, read_conn).await;
        });
        let (message_tx, write_rx) = mpsc::channel(1);
        let write_task = tokio::spawn(async move {
            if let Err(err) = Self::write_loop(send, write_rx).await {
                debug!("Peer writer failed: {err}");
                conn.close(0u32.into(), b"peer writer ended");
            }
        });

        Ok(Self {
            message_tx,
            message_rx,
            read_task,
            write_task,
        })
    }

    async fn read_loop(
        mut receive: RecvStream,
        message_tx: mpsc::Sender<Result<PeerMessage>>,
        conn: IrohEndpointConnection,
    ) -> Result<()> {
        loop {
            let result = Self::read_next(&mut receive).await;
            let failed = result.is_err();
            if failed {
                conn.close(0u32.into(), b"peer reader ended");
            }
            message_tx.send(result).await?;
            if failed {
                return Ok(());
            }
        }
    }

    async fn read_next(receive: &mut RecvStream) -> Result<PeerMessage> {
        let mut message_len_buf = [0; 4];
        Self::read_exact(receive, &mut message_len_buf).await?;
        let byte_count = u32::from_be_bytes(message_len_buf);

        let mut bytes = vec![0; byte_count as usize];
        Self::read_exact(receive, &mut bytes).await?;
        from_bytes(&bytes).context("Could not read the peer's message; the peer probably runs a different teamtype version")
    }

    /// Times out only when bytes stop arriving, allowing large sync messages to make progress.
    async fn read_exact(receive: &mut RecvStream, mut bytes: &mut [u8]) -> Result<()> {
        while !bytes.is_empty() {
            let count = timeout(PEER_TIMEOUT, receive.read(bytes))
                .await??
                .context("Peer stream ended")?;
            bytes = &mut bytes[count..];
        }
        Ok(())
    }

    // 🧑 "Also not syncing after a while"
    /// Writes independently of document processing. Flow control may pause a write indefinitely;
    /// only the reader's time spent waiting for bytes determines peer inactivity.
    async fn write_loop(
        mut send: SendStream,
        mut message_rx: mpsc::Receiver<PeerMessage>,
    ) -> Result<()> {
        loop {
            let message = match timeout(Duration::from_secs(2), message_rx.recv()).await {
                Ok(Some(message)) => message,
                Ok(None) => return Ok(()),
                Err(_) => PeerMessage::Heartbeat,
            };
            let bytes = to_allocvec(&message).context("Failed to convert PeerMessage to bytes")?;
            let byte_count = u32::try_from(bytes.len())?;
            send.write_all(&byte_count.to_be_bytes()).await?;
            send.write_all(&bytes).await?;
        }
    }
}

#[async_trait]
impl Connection<PeerMessage> for PeerMessageStream {
    async fn send(&mut self, message: PeerMessage) -> Result<()> {
        self.message_tx
            .send(message)
            .await
            .context("Peer writer ended")
    }

    async fn next(&mut self) -> Result<PeerMessage> {
        self.message_rx
            .recv()
            .await
            .context("Failed to await next peer message")?
    }
}
