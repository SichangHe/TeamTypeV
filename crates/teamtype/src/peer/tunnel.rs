// SPDX-FileCopyrightText: 2026 Sichang He
//
// SPDX-License-Identifier: AGPL-3.0-or-later

// 🧑 "can you tunnel it together with TT? Let's leave security alone for now and have a prototype
// that works"
//! Forwards TCP connections from a guest's localhost to a port on the sharer's machine, over the
//! sharer's Iroh endpoint, for example to reach a web editor running next to the sharer.
//!
//! Every TCP connection becomes one stream that starts with the sharer's passphrase.

use std::str::FromStr;

use anyhow::{Context, Result};
use iroh::endpoint::{Connection as IrohEndpointConnection, presets};
use iroh::{Endpoint, SecretKey};
use tokio::net::{TcpListener, TcpStream};
use tracing::{debug, info, warn};

use super::SecretAddress;

pub const ALPN: &[u8] = b"/teamtype-tunnel/0";

/// At the sharer: forwards each stream of `conn` to `port` on localhost.
pub async fn serve(conn: IrohEndpointConnection, passphrase: SecretKey, port: u16) {
    while let Ok((mut send, mut recv)) = conn.accept_bi().await {
        let passphrase = passphrase.clone();
        tokio::spawn(async move {
            let mut received = [0; 32];
            if recv.read_exact(&mut received).await.is_err()
                || !constant_time_eq::constant_time_eq(&received, &passphrase.to_bytes())
            {
                warn!("Rejected a tunnel stream with a wrong passphrase.");
                return;
            }
            let tcp = match TcpStream::connect(("127.0.0.1", port)).await {
                Ok(tcp) => tcp,
                Err(err) => {
                    warn!("Tunnel could not reach port {port}: {err}");
                    return;
                }
            };
            let (mut tcp_read, mut tcp_write) = tcp.into_split();
            let _ = tokio::join!(tokio::io::copy(&mut recv, &mut tcp_write), async {
                let _ = tokio::io::copy(&mut tcp_read, &mut send).await;
                let _ = send.finish();
            });
        });
    }
}

/// At a guest: forwards `local_port` on localhost to the port the sharer forwards.
pub async fn run(secret_address: &str, local_port: u16) -> Result<()> {
    let address = SecretAddress::from_str(secret_address)?;
    let endpoint = Endpoint::builder(presets::N0).bind().await?;
    let listener = TcpListener::bind(("127.0.0.1", local_port))
        .await
        .with_context(|| format!("Could not listen on port {local_port}"))?;
    let mut conn = endpoint
        .connect(address.endpoint_addr.clone(), ALPN)
        .await
        .context("Could not reach the sharer")?;
    info!(
        "Tunnel ready: open http://localhost:{local_port} in your browser. Press Ctrl+C to stop."
    );
    loop {
        let (tcp, _) = listener.accept().await?;
        let (mut send, mut recv) = match conn.open_bi().await {
            Ok(streams) => streams,
            Err(err) => {
                debug!("Tunnel connection lost ({err}); reconnecting.");
                conn = endpoint
                    .connect(address.endpoint_addr.clone(), ALPN)
                    .await
                    .context("Could not reach the sharer")?;
                conn.open_bi().await?
            }
        };
        let passphrase = address.passphrase.to_bytes();
        tokio::spawn(async move {
            if send.write_all(&passphrase).await.is_err() {
                return;
            }
            let (mut tcp_read, mut tcp_write) = tcp.into_split();
            let _ = tokio::join!(tokio::io::copy(&mut recv, &mut tcp_write), async {
                let _ = tokio::io::copy(&mut tcp_read, &mut send).await;
                let _ = send.finish();
            });
        });
    }
}
