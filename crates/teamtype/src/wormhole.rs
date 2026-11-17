// SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::{borrow::Cow, str::FromStr, time::Duration};

use anyhow::Result;
use docstr::docstr;
use magic_wormhole::{AppConfig, AppID, Code, MailboxConnection, Wormhole, transfer};
use tokio::time::sleep;
use tracing::{info, warn};

use crate::perf;

const NETWORK_RETRY: Duration = Duration::from_mins(5);

pub async fn put_secret_address_into_wormhole(address: &str, magic_wormhole_relay: Option<String>) {
    let payload: Vec<u8> = address.into();
    let config = build_magic_wormhole_config(magic_wormhole_relay);

    tokio::spawn(async move {
        loop {
            let timer = perf::timer("wormhole.create_code");
            let created = MailboxConnection::create(config.clone(), 2).await;
            timer.done(&[("ok", u64::from(created.is_ok()))]);
            let Ok(mailbox_connection) = created else {
                warn!(
                    "Failed to register a new join code via Magic Wormhole. Automatic retry in {:?}. Peers who joined before can still re-connect without a code.",
                    NETWORK_RETRY
                );
                sleep(NETWORK_RETRY).await;
                continue;
            };
            let code = mailbox_connection.code().clone();

            info!(
                "{}",
                &docstr!(format!
                        /// One other person can use this to connect to you:
                        ///
                        ///    teamtypev join {code}
                        ///
                )
            );

            if let Ok(mut wormhole) = Wormhole::connect(mailbox_connection).await {
                let _ = wormhole.send(payload.clone()).await;
            } else {
                warn!("Failed to share secret address. Did your peer mistype the join code?");
            }

            // Print a new join code in the next iteration of the for loop, to allow more people
            // to join.
            sleep(Duration::from_millis(500)).await;
        }
    });
}

pub async fn get_secret_address_from_wormhole(
    code: &str,
    magic_wormhole_relay: Option<String>,
) -> Result<String> {
    let config = build_magic_wormhole_config(magic_wormhole_relay);

    let timer = perf::timer("wormhole.mailbox");
    let mailbox = MailboxConnection::connect(config, Code::from_str(code)?, false).await?;
    timer.done(&[]);
    let timer = perf::timer("wormhole.key_exchange");
    let mut wormhole = Wormhole::connect(mailbox).await?;
    timer.done(&[]);
    let timer = perf::timer("wormhole.receive");
    let bytes = wormhole.receive().await?;
    timer.done(&[("bytes", bytes.len() as u64)]);
    Ok(String::from_utf8(bytes)?)
}

fn build_magic_wormhole_config(
    magic_wormhole_relay: Option<String>,
) -> AppConfig<transfer::AppVersion> {
    let mut config = transfer::APP_CONFIG.id(AppID::new("teamtypev"));

    if let Some(url) = magic_wormhole_relay {
        info!("Using non-default Magic Wormhole relay url {}", url);
        config = config.rendezvous_url(Cow::Owned(url));
    }
    config
}
