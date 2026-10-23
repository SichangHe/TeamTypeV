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
use iroh::endpoint::{Connection as IrohEndpointConnection, RecvStream, SendStream, presets};
use iroh::{Endpoint, SecretKey};
use tokio::io::AsyncWriteExt;
use tokio::net::{TcpListener, TcpStream};
use tracing::{debug, info, warn};

use super::SecretAddress;

pub const ALPN: &[u8] = b"/teamtype-tunnel/0";

/// Preserves independent TCP half-closes in both directions.
async fn forward(tcp: TcpStream, mut send: SendStream, mut recv: RecvStream) {
    let (mut tcp_read, mut tcp_write) = tcp.into_split();
    let _ = tokio::join!(
        async {
            let _ = tokio::io::copy(&mut recv, &mut tcp_write).await;
            let _ = tcp_write.shutdown().await;
        },
        async {
            let _ = tokio::io::copy(&mut tcp_read, &mut send).await;
            let _ = send.finish();
        }
    );
}

/// At the sharer: forwards each stream of `conn` to `port` on localhost.
pub async fn serve(conn: IrohEndpointConnection, passphrase: SecretKey, port: u16) {
    while let Ok((send, mut recv)) = conn.accept_bi().await {
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
            forward(tcp, send, recv).await;
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
        let (mut send, recv) = match conn.open_bi().await {
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
            forward(tcp, send, recv).await;
        });
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use futures::FutureExt;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::time::timeout;

    use super::*;

    async fn endpoint() -> Result<Endpoint> {
        Ok(Endpoint::builder(presets::Minimal)
            .alpns(vec![ALPN.to_vec()])
            .bind_addr("127.0.0.1:0")?
            .bind()
            .await?)
    }

    #[tokio::test]
    async fn authentication_and_independent_tcp_streams() -> Result<()> {
        timeout(Duration::from_secs(10), async {
            let listener = TcpListener::bind("127.0.0.1:0").await?;
            let host = endpoint().await?;
            let guest = endpoint().await?;
            let (conn, incoming) = tokio::join!(guest.connect(host.addr(), ALPN), async {
                host.accept().await.expect("host is open").await
            });
            let conn = conn?;
            let passphrase = SecretKey::from_bytes(&[42; 32]);
            let server = tokio::spawn(serve(
                incoming?,
                passphrase.clone(),
                listener.local_addr()?.port(),
            ));

            for invalid in [vec![0; 32], passphrase.to_bytes()[..31].to_vec()] {
                let (mut send, mut recv) = conn.open_bi().await?;
                send.write_all(&invalid).await?;
                send.finish()?;
                assert!(recv.read_to_end(1).await?.is_empty());
                assert!(listener.accept().now_or_never().is_none());
            }

            let mut streams = vec![];
            for request in [b"first\0request".as_slice(), b"second request"] {
                let (mut send, recv) = conn.open_bi().await?;
                let key = passphrase.to_bytes();
                send.write_all(&key[..13]).await?;
                send.write_all(&key[13..]).await?;
                send.write_all(request).await?;
                send.finish()?;
                let (mut tcp, _) = listener.accept().await?;
                let mut received = vec![0; request.len()];
                tcp.read_exact(&mut received).await?;
                assert_eq!(received, request);
                streams.push((tcp, recv, request));
            }
            for (mut tcp, mut recv, request) in streams.into_iter().rev() {
                let mut response = b"response\0bytes".to_vec();
                response.extend_from_slice(request);
                tcp.write_all(&response).await?;
                tcp.shutdown().await?;
                assert_eq!(recv.read_to_end(100).await?, response);
            }

            conn.close(0_u32.into(), b"done");
            server.await?;
            guest.close().await;
            host.close().await;
            anyhow::Ok(())
        })
        .await?
    }

    #[tokio::test]
    async fn finished_request_delivers_eof_to_tcp_backend() -> Result<()> {
        timeout(Duration::from_secs(10), async {
            let listener = TcpListener::bind("127.0.0.1:0").await?;
            let host = endpoint().await?;
            let guest = endpoint().await?;
            let (conn, incoming) = tokio::join!(guest.connect(host.addr(), ALPN), async {
                host.accept()
                    .await
                    .context("Host is closed")?
                    .await
                    .context("Could not accept tunnel")
            });
            let conn = conn?;
            let passphrase = SecretKey::from_bytes(&[42; 32]);
            let server = tokio::spawn(serve(
                incoming?,
                passphrase.clone(),
                listener.local_addr()?.port(),
            ));
            let (mut send, _recv) = conn.open_bi().await?;
            send.write_all(&passphrase.to_bytes()).await?;
            send.write_all(b"request").await?;
            send.finish()?;
            let (mut tcp, _) = listener.accept().await?;
            let mut request = [0; 7];
            tcp.read_exact(&mut request).await?;
            assert_eq!(&request, b"request");
            let eof = timeout(Duration::from_secs(1), tcp.read(&mut [0])).await;
            conn.close(0_u32.into(), b"done");
            server.await?;
            guest.close().await;
            host.close().await;
            assert_eq!(
                eof.context("Finished guest request did not reach the TCP backend as EOF")??,
                0
            );
            anyhow::Ok(())
        })
        .await?
    }

    #[tokio::test]
    async fn finished_response_delivers_eof_while_client_keeps_sending() -> Result<()> {
        timeout(Duration::from_secs(10), async {
            let host = endpoint().await?;
            let guest = endpoint().await?;
            let (conn, incoming) = tokio::join!(guest.connect(host.addr(), ALPN), async {
                host.accept()
                    .await
                    .context("Host closed")?
                    .await
                    .context("Accept tunnel")
            });
            let conn = conn?;
            let incoming = incoming?;
            let listener = TcpListener::bind("127.0.0.1:0").await?;
            let mut client = TcpStream::connect(listener.local_addr()?).await?;
            let (tcp, _) = listener.accept().await?;
            let (mut send, recv) = conn.open_bi().await?;
            send.write_all(b"request").await?;
            let forwarding = tokio::spawn(forward(tcp, send, recv));
            let (mut send, mut recv) = incoming.accept_bi().await?;
            let mut request = [0; 7];
            recv.read_exact(&mut request).await?;
            assert_eq!(&request, b"request");
            send.write_all(b"response").await?;
            send.finish()?;
            let mut response = vec![];
            client.read_to_end(&mut response).await?;
            assert_eq!(response, b"response");
            client.write_all(b"after response").await?;
            client.shutdown().await?;
            assert_eq!(recv.read_to_end(100).await?, b"after response");
            forwarding.await?;
            conn.close(0_u32.into(), b"done");
            guest.close().await;
            host.close().await;
            anyhow::Ok(())
        })
        .await?
    }

    #[tokio::test]
    async fn invalid_secret_address_is_rejected() {
        assert!(run("not a secret address", 0).await.is_err());
    }
}
