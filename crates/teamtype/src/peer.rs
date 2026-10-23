// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

//! This module provides a [`ConnectionManager`], which can be used to connect to other daemons.

use std::collections::HashMap;
use std::fs::{self, File, OpenOptions};
use std::future::IntoFuture;
use std::io::{Read, Write};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::Path;
use std::str::FromStr;
use std::time::Duration;

use anyhow::bail;
use anyhow::{Context, Result};
use async_trait::async_trait;
use futures::{StreamExt, stream::FuturesUnordered};
use iroh::address_lookup::DnsAddressLookup;
use iroh::address_lookup::pkarr::PkarrPublisher;
use iroh::endpoint::{
    Connection as IrohEndpointConnection, RecvStream, RelayMode, RelayStatus, SendStream,
    TransportAddrInfo, presets,
};
use iroh::{Endpoint, EndpointAddr, PublicKey, RelayMap, RelayUrl, SecretKey, Watcher};
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
const RECONNECT_TIMEOUT: Duration = Duration::from_secs(2);
const CONNECT_TIMEOUT: Duration = Duration::from_secs(15);
const RETRY_CONNECT_TIMEOUT: Duration = Duration::from_secs(8);
const ENDPOINT_CLOSE_TIMEOUT: Duration = Duration::from_secs(2);
const MAX_REFRESH_DELAY: Duration = Duration::from_mins(5);

/// Limits endpoint churn while allowing relay setup to finish.
struct RelayRecovery {
    since: tokio::time::Instant,
    delay: Duration,
    restored: bool,
}

impl RelayRecovery {
    fn new() -> Self {
        Self {
            since: tokio::time::Instant::now(),
            delay: CONNECT_TIMEOUT,
            restored: false,
        }
    }

    fn due(&mut self, live: bool, pending: bool) -> bool {
        if live {
            *self = Self::new();
        }
        !live
            && !pending
            && self.since.elapsed() >= CONNECT_TIMEOUT
            && (self.restored
                || (self.delay <= MAX_REFRESH_DELAY && self.since.elapsed() >= self.delay))
    }

    fn network_restored(&mut self) {
        self.delay = CONNECT_TIMEOUT;
        self.restored = true;
    }

    fn attempted(&mut self) {
        self.since = tokio::time::Instant::now();
        self.delay *= 2;
        self.restored = false;
    }
}

struct SecretAddress {
    endpoint_addr: EndpointAddr,
    passphrase: SecretKey,
}

impl SecretAddress {
    fn reconnect_addr(&self, previous_attempts: usize) -> EndpointAddr {
        if previous_attempts > 0 && previous_attempts.is_multiple_of(3) {
            EndpointAddr::from_parts(
                self.endpoint_addr.id,
                self.endpoint_addr
                    .addrs
                    .iter()
                    .filter(|addr| addr.is_relay())
                    .cloned(),
            )
        } else {
            self.endpoint_addr.clone()
        }
    }
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
            .alpns(vec![ALPN.to_vec(), tunnel::ALPN.to_vec()])
            .transport_config(
                iroh::endpoint::QuicTransportConfig::builder()
                    .enable_segmentation_offload(false)
                    .build(),
            );

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
    Connected {
        secret_address: SecretAddress,
        response_tx: Option<oneshot::Sender<Result<()>>>,
        previous_attempts: usize,
        generation: u64,
        result: Result<IrohEndpointConnection>,
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
    connecting: HashMap<PublicKey, JoinHandle<()>>,
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
            connecting: HashMap::new(),
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
                if previous_attempts > 0 && previous_attempts.is_multiple_of(3) {
                    self.endpoint.dns_resolver()?.reset();
                }
                let endpoint_addr = secret_address.reconnect_addr(previous_attempts);
                let connect_timeout = if response_tx.is_some() {
                    CONNECT_TIMEOUT
                } else {
                    RETRY_CONNECT_TIMEOUT
                };
                let endpoint = self.endpoint.clone();
                let message_tx = self.message_tx.clone();
                self.connecting.insert(
                    peer_id,
                    tokio::spawn(async move {
                        let result =
                            timeout(connect_timeout, endpoint.connect(endpoint_addr, ALPN))
                                .await
                                .map_err(anyhow::Error::from)
                                .and_then(|result| result.map_err(anyhow::Error::from));
                        let _ = message_tx
                            .send(EndpointMessage::Connected {
                                secret_address,
                                response_tx,
                                previous_attempts,
                                generation,
                                result,
                            })
                            .await;
                    }),
                );
            }
            EndpointMessage::Connected {
                mut secret_address,
                response_tx,
                previous_attempts,
                generation,
                result,
            } => {
                let peer_id = secret_address.endpoint_addr.id;
                if self.peer_generations.get(&peer_id) != Some(&generation) {
                    debug!("Dropping superseded connection to peer {peer_id}.");
                    if let Some(response_tx) = response_tx {
                        let _ = response_tx.send(Ok(()));
                    }
                    return Ok(());
                }
                self.connecting.remove(&peer_id);
                let conn = match result {
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
                        tokio::spawn(Self::reconnect(
                            self.message_tx.clone(),
                            secret_address,
                            previous_attempts,
                            generation,
                        ));
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

                if let Some(remote) = self.endpoint.remote_info(peer_id).await {
                    secret_address.endpoint_addr = EndpointAddr::from_parts(
                        peer_id,
                        remote.into_addrs().map(TransportAddrInfo::into_addr),
                    );
                }

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

    // 🧑 "Also not syncing after a while"
    /// Clears relay backoff while disconnected, including at the sharer. Handshakes run
    /// concurrently so a stalled incoming connection cannot delay the relay check.
    async fn run(&mut self) {
        let network_monitor = match netwatch::netmon::Monitor::new().await {
            Ok(monitor) => Some(monitor),
            Err(err) => {
                warn!("Could not monitor network availability: {err}");
                None
            }
        };
        let mut network_was_up = true;
        let mut relay_check = tokio::time::interval(RECONNECT_TIMEOUT);
        relay_check.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
        let mut incoming_connections = FuturesUnordered::new();
        let mut tunnel_tasks = Vec::new();
        let mut recovery = RelayRecovery::new();
        loop {
            tokio::select! {
                biased;
                _ = relay_check.tick() => {
                    let network_up = network_monitor.as_ref().is_none_or(|monitor| {
                        let state = monitor.interface_state().get();
                        state.have_v4 || state.have_v6
                    });
                    if network_up && !network_was_up {
                        debug!("Network returned; refreshing disconnected relay state.");
                        recovery.network_restored();
                        if let Ok(resolver) = self.endpoint.dns_resolver() {
                            resolver.reset();
                        }
                    }
                    network_was_up = network_up;
                    tunnel_tasks.retain(|task: &JoinHandle<()>| !task.is_finished());
                    let live = self.peer_tasks.values().any(|task| !task.is_finished())
                        || !tunnel_tasks.is_empty()
                        || self.endpoint.home_relay_status().get().iter().any(RelayStatus::is_connected);
                    self.connecting.retain(|_, task| !task.is_finished());
                    let pending = !incoming_connections.is_empty()
                        || (!recovery.restored && !self.connecting.is_empty());
                    if recovery.due(live, pending) && network_up
                        && !self.peer_generations.is_empty()
                    {
                        recovery.attempted();
                        match ConnectionManager::bind_endpoint(
                            &self.app_config,
                            self.endpoint.secret_key().clone(),
                        ).await {
                            Ok(endpoint) => {
                                debug!("Refreshing the disconnected relay endpoint.");
                                let previous_endpoint = std::mem::replace(&mut self.endpoint, endpoint);
                                let _ = timeout(ENDPOINT_CLOSE_TIMEOUT, previous_endpoint.close()).await;
                            }
                            Err(err) => warn!("Could not refresh the disconnected endpoint: {err:#}"),
                        }
                    }
                }
                maybe_incoming = self.endpoint.accept() => {
                    match maybe_incoming {
                        Some(incoming) => {
                            incoming_connections.push(timeout(CONNECT_TIMEOUT, incoming.into_future()));
                        }
                        None => {
                            // Endpoint was closed. Let's shut down.
                            break
                        }
                    }
                }
                Some(result) = incoming_connections.next() => {
                    match result {
                        Ok(Ok(conn)) => {
                            if conn.alpn() == tunnel::ALPN {
                                if let Some(port) = self.forward_port {
                                    debug!("Tunnel connected: {}", conn.remote_id());
                                    tunnel_tasks.push(tokio::spawn(tunnel::serve(conn, self.my_passphrase.clone(), port)));
                                }
                            } else {
                                self.handle_incoming_connection(conn);
                            }
                        }
                        Ok(Err(err)) => debug!("Error while accepting peer connection: {err}"),
                        Err(err) => debug!("Error while accepting peer connection: {err}"),
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

#[cfg(test)]
mod recovery_tests {
    use super::*;

    #[test]
    fn rediscovery_keeps_relay_hint() -> Result<()> {
        let relay: RelayUrl = "https://relay.example.com".parse()?;
        let address = SecretAddress {
            endpoint_addr: EndpointAddr::new(SecretKey::generate().public())
                .with_relay_url(relay.clone())
                .with_ip_addr("127.0.0.1:1234".parse()?),
            passphrase: SecretKey::generate(),
        };
        assert_eq!(address.reconnect_addr(2), address.endpoint_addr);
        let fresh = address.reconnect_addr(3);
        assert_eq!(fresh.relay_urls().collect::<Vec<_>>(), vec![&relay]);
        assert_eq!(fresh.ip_addrs().count(), 0);
        Ok(())
    }

    #[tokio::test]
    async fn tunnel_survives_blocked_relay_without_sync_peers() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::create_dir(dir.path().join(".teamtype"))?;
        let config = AppConfig {
            base_dir: dir.path().to_path_buf(),
            iroh_relay: Some("http://127.0.0.1:9".to_owned()),
            ..AppConfig::default()
        };
        let endpoint = ConnectionManager::bind_endpoint(&config, SecretKey::generate()).await?;
        let address = endpoint.addr();
        let client = Endpoint::builder(presets::Minimal).bind().await?;
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await?;
        let port = listener.local_addr()?.port();
        let echo = tokio::spawn(async move {
            let (mut tcp, _) = listener.accept().await?;
            let (mut read, mut write) = tcp.split();
            tokio::io::copy(&mut read, &mut write).await
        });
        let passphrase = SecretKey::generate();
        let (tx, rx) = mpsc::channel(1);
        let doc = DocumentActorHandle::new(&config, true, true, false);
        let mut actor =
            EndpointActor::new(endpoint.clone(), rx, tx, doc, passphrase.clone(), config);
        actor.forward_port = Some(port);
        actor.peer_generations.insert(client.id(), 1);
        let task = tokio::spawn(async move { actor.run().await });
        let conn = timeout(CONNECT_TIMEOUT, client.connect(address, tunnel::ALPN)).await??;
        let (mut send, mut recv) = conn.open_bi().await?;
        send.write_all(&passphrase.to_bytes()).await?;
        send.write_all(b"before").await?;
        let mut bytes = [0; 6];
        timeout(PEER_TIMEOUT, recv.read_exact(&mut bytes)).await??;
        assert_eq!(&bytes, b"before");
        sleep(CONNECT_TIMEOUT + RECONNECT_TIMEOUT).await;
        assert!(!endpoint.is_closed());
        assert!(
            endpoint
                .home_relay_status()
                .get()
                .iter()
                .all(|relay| !relay.is_connected())
        );
        send.write_all(b"after!").await?;
        timeout(PEER_TIMEOUT, recv.read_exact(&mut bytes)).await??;
        assert_eq!(&bytes, b"after!");
        conn.close(0u32.into(), b"test finished");
        task.abort();
        echo.abort();
        let _ = timeout(ENDPOINT_CLOSE_TIMEOUT, endpoint.close()).await;
        let _ = timeout(ENDPOINT_CLOSE_TIMEOUT, client.close()).await;
        Ok(())
    }

    #[tokio::test]
    async fn relay_setup_and_offline_backoff() {
        let mut recovery = RelayRecovery::new();
        recovery.since -= Duration::from_secs(5);
        assert!(!recovery.due(false, false));
        recovery.since -= Duration::from_secs(10);
        assert!(recovery.due(false, false));
        recovery.attempted();
        assert_eq!(recovery.delay, Duration::from_secs(30));
        let mut replacements = 1;
        for _ in 0..900 {
            recovery.since -= RECONNECT_TIMEOUT;
            if recovery.due(false, false) {
                recovery.attempted();
                replacements += 1;
            }
        }
        assert_eq!(replacements, 5, "offline replacements: {replacements}");
        recovery.since -= Duration::from_hours(1);
        assert!(!recovery.due(false, false));
        assert!(!recovery.due(true, false));
        assert_eq!(recovery.delay, CONNECT_TIMEOUT);
    }

    #[tokio::test]
    async fn direct_tunnels_and_handshakes_prevent_replacement() {
        let mut recovery = RelayRecovery::new();
        recovery.since -= MAX_REFRESH_DELAY;
        assert!(!recovery.due(false, true));
        assert!(recovery.due(false, false));
        assert!(!recovery.due(true, false));
    }

    #[tokio::test]
    async fn restoration_resets_backoff_but_keeps_minimum_age() {
        let mut recovery = RelayRecovery::new();
        recovery.network_restored();
        assert!(!recovery.due(false, false));
        recovery.since -= CONNECT_TIMEOUT;
        recovery.restored = false;
        recovery.delay = MAX_REFRESH_DELAY * 2;
        assert!(!recovery.due(false, false));
        recovery.network_restored();
        assert_eq!(recovery.delay, CONNECT_TIMEOUT);
        assert!(!recovery.due(false, true));
        assert!(recovery.due(false, false));
        recovery.attempted();
        assert!(!recovery.restored);
        assert!(!recovery.due(false, false));
    }

    #[tokio::test]
    async fn slow_connect_finishes_within_deadline() -> Result<()> {
        let server = Endpoint::builder(presets::Minimal)
            .alpns(vec![ALPN.to_vec()])
            .bind()
            .await?;
        let client = Endpoint::builder(presets::Minimal).bind().await?;
        let address = server.addr();
        let accept = tokio::spawn(async move {
            sleep(Duration::from_secs(5)).await;
            let incoming = server.accept().await.context("server closed")?;
            let conn = incoming.await?;
            conn.closed().await;
            server.close().await;
            Ok::<_, anyhow::Error>(())
        });
        let conn = timeout(RETRY_CONNECT_TIMEOUT, client.connect(address, ALPN)).await??;
        conn.close(0u32.into(), b"test finished");
        timeout(ENDPOINT_CLOSE_TIMEOUT, client.close()).await?;
        timeout(CONNECT_TIMEOUT, accept).await???;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    async fn connected_streams() -> Result<(
        Endpoint,
        Endpoint,
        IrohEndpointConnection,
        SendStream,
        RecvStream,
    )> {
        let server = Endpoint::builder(presets::Minimal)
            .alpns(vec![ALPN.to_vec()])
            .bind_addr("127.0.0.1:0")?
            .bind()
            .await?;
        let client = Endpoint::builder(presets::Minimal)
            .bind_addr("127.0.0.1:0")?
            .bind()
            .await?;
        let (outgoing, incoming) = tokio::join!(client.connect(server.addr(), ALPN), async {
            server
                .accept()
                .await
                .context("No incoming connection")?
                .await
                .context("Accept failed")
        });
        let outgoing = outgoing?;
        let incoming = incoming?;
        let (mut send, _) = outgoing.open_bi().await?;
        send.write_all(&[0]).await?;
        let (_, mut receive) = incoming.accept_bi().await?;
        receive.read_exact(&mut [0]).await?;
        Ok((server, client, incoming, send, receive))
    }

    #[tokio::test]
    async fn idle_writer_sends_heartbeats_and_preserves_message_framing() -> Result<()> {
        timeout(Duration::from_secs(15), async {
            let (_server, _client, _conn, send, mut receive) = connected_streams().await?;
            let (tx, rx) = mpsc::channel(1);
            let writer = tokio::spawn(PeerMessageStream::write_loop(send, rx));
            assert!(matches!(PeerMessageStream::read_next(&mut receive).await?, PeerMessage::Heartbeat));
            tx.send(PeerMessage::Hello("history".into())).await?;
            assert!(matches!(PeerMessageStream::read_next(&mut receive).await?, PeerMessage::Hello(id) if id == "history"));
            assert!(matches!(PeerMessageStream::read_next(&mut receive).await?, PeerMessage::Heartbeat));
            drop(tx);
            writer.await??;
            Ok::<_, anyhow::Error>(())
        }).await?
    }

    #[tokio::test]
    async fn stalled_partial_frame_closes_connection_for_reconnect() -> Result<()> {
        timeout(Duration::from_secs(15), async {
            let (_server, _client, conn, mut send, receive) = connected_streams().await?;
            let (tx, mut rx) = mpsc::channel(1);
            let reader = tokio::spawn(PeerMessageStream::read_loop(receive, tx, conn.clone()));
            send.write_all(&[0, 0]).await?;
            let error = rx
                .recv()
                .await
                .context("Reader dropped its result")?
                .err()
                .context("Stalled frame was accepted")?;
            assert!(error.is::<tokio::time::error::Elapsed>(), "{error:#}");
            assert!(conn.close_reason().is_some());
            reader.await??;
            Ok::<_, anyhow::Error>(())
        })
        .await?
    }

    #[tokio::test]
    async fn stalled_peer_reconnects_with_a_new_generation() -> Result<()> {
        timeout(Duration::from_secs(20), async {
            let server = Endpoint::builder(presets::Minimal)
                .alpns(vec![ALPN.to_vec()])
                .bind_addr("127.0.0.1:0")?
                .bind()
                .await?;
            let client = Endpoint::builder(presets::Minimal)
                .bind_addr("127.0.0.1:0")?
                .bind()
                .await?;
            let directory = tempfile::tempdir()?;
            fs::create_dir(directory.path().join(".teamtype"))?;
            let config = AppConfig {
                base_dir: directory.path().into(),
                ..AppConfig::default()
            };
            let document_handle = DocumentActorHandle::new(&config, false, false, true);
            let (message_tx, message_rx) = mpsc::channel(1);
            let passphrase = SecretKey::from_bytes(&[42; 32]);
            let mut actor = EndpointActor::new(
                client,
                message_rx,
                message_tx,
                document_handle,
                passphrase.clone(),
                config,
            );
            let (response_tx, response_rx) = oneshot::channel();
            let initial = EndpointMessage::Connect {
                secret_address: SecretAddress {
                    endpoint_addr: server.addr(),
                    passphrase: passphrase.clone(),
                },
                response_tx: Some(response_tx),
                previous_attempts: 0,
                generation: None,
            };
            // Connects run in a task that reports back through the actor's own channel.
            let (connected, incoming) = tokio::join!(
                async {
                    actor.handle_message(initial).await?;
                    let finished = actor.message_rx.recv().await.context("No connect result")?;
                    actor.handle_message(finished).await
                },
                async {
                    server
                        .accept()
                        .await
                        .context("No initial connection")?
                        .await
                        .context("Initial accept failed")
                }
            );
            connected?;
            response_rx.await??;
            let incoming = incoming?;
            let (_silent_send, mut receive) = incoming.accept_bi().await?;
            let mut received_passphrase = [0; 32];
            receive.read_exact(&mut received_passphrase).await?;
            assert_eq!(received_passphrase, passphrase.to_bytes());
            let generation = actor.peer_generations[&server.id()];

            let reconnect = actor
                .message_rx
                .recv()
                .await
                .context("No reconnect request")?;
            assert!(matches!(&reconnect, EndpointMessage::Connect {
                previous_attempts: 1, generation: Some(previous), ..
            } if *previous == generation));
            let (connected, replacement) = tokio::join!(
                async {
                    actor.handle_message(reconnect).await?;
                    let finished = actor
                        .message_rx
                        .recv()
                        .await
                        .context("No reconnect result")?;
                    actor.handle_message(finished).await
                },
                async {
                    server
                        .accept()
                        .await
                        .context("No replacement connection")?
                        .await
                        .context("Replacement accept failed")
                }
            );
            connected?;
            let replacement = replacement?;
            assert!(actor.peer_generations[&server.id()] > generation);
            let (_send, mut receive) = replacement.accept_bi().await?;
            receive.read_exact(&mut received_passphrase).await?;
            assert_eq!(received_passphrase, passphrase.to_bytes());
            for task in actor.peer_tasks.values() {
                task.abort();
            }
            Ok::<_, anyhow::Error>(())
        })
        .await?
    }

    #[tokio::test]
    async fn progressing_frame_can_take_longer_than_peer_timeout() -> Result<()> {
        timeout(Duration::from_secs(20), async {
            let (_server, _client, _conn, mut send, mut receive) = connected_streams().await?;
            let bytes = to_allocvec(&PeerMessage::Hello("progress".into()))?;
            let sender = tokio::spawn(async move {
                send.write_all(&u32::try_from(bytes.len())?.to_be_bytes()).await?;
                for byte in bytes {
                    sleep(Duration::from_secs(1)).await;
                    send.write_all(&[byte]).await?;
                }
                Ok::<_, anyhow::Error>(send)
            });
            let started = tokio::time::Instant::now();
            assert!(matches!(PeerMessageStream::read_next(&mut receive).await?, PeerMessage::Hello(id) if id == "progress"));
            assert!(started.elapsed() > PEER_TIMEOUT);
            let _send = sender.await??;
            Ok::<_, anyhow::Error>(())
        }).await?
    }
}
