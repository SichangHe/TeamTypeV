// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 axelmartensson <axel.martensson@hotmail.com>
// SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::io::Write;
use std::io::{stdin, stdout};
use std::path::{Path, PathBuf};
use std::process::exit;
use std::{env, panic};

use anyhow::bail;
use anyhow::{Context, Result};
use clap::{CommandFactory as _, FromArgMatches as _};
use microxdg::XdgApp;
use teamtype::jsonrpc_forwarder::{JSONRPCForwarder, UnixJSONRPCForwarder};
use teamtype::{
    config::{self, AppConfig},
    daemon::Daemon,
    logging, sandbox,
};
use tempfile::{TempDir, tempdir_in};
use tokio::signal;
use tracing::{debug, info, warn};

use self::cli::{Cli, Commands, ShareJoinFlags};

mod agent_edit;
mod cli;

fn has_ethersync_directory(dir: &Path) -> bool {
    let ethersync_dir = dir.join(config::LEGACY_CONFIG_DIR);
    // Using the sandbox method here is technically unnecessary,
    // but we want to really run all path operations through the sandbox module.
    sandbox::exists(dir, &ethersync_dir).expect("Failed to check") && ethersync_dir.is_dir()
}

fn has_teamtype_directory(dir: &Path) -> bool {
    let teamtype_dir = dir.join(config::CONFIG_DIR);
    // Using the sandbox method here is technically unnecessary,
    // but we want to really run all path operations through the sandbox module.
    sandbox::exists(dir, &teamtype_dir).expect("Failed to check") && teamtype_dir.is_dir()
}

#[tokio::main]
async fn main() -> Result<()> {
    let default_panic = panic::take_hook();
    panic::set_hook(Box::new(move |info| {
        default_panic(info);
        exit(1);
    }));

    let version = option_env!("TEAMTYPE_VERSION").unwrap_or(env!("CARGO_PKG_VERSION"));
    let arg_matches = Cli::command().version(version).get_matches();
    let cli = match Cli::from_arg_matches(&arg_matches) {
        Ok(cli) => cli,
        Err(e) => e.exit(),
    };

    logging::initialize().context("Failed to initialize logging")?;

    if let Commands::Tunnel {
        secret_address,
        port,
    } = &cli.command
    {
        return teamtype::peer::run_tunnel(secret_address, *port).await;
    }

    if let Commands::Git { args } = &cli.command {
        let code = teamtype::git_forward::client(cli.directory.as_deref(), args.clone()).await?;
        exit(code);
    }

    let temporary_directory = get_temporary_directory(&cli)?;
    let directory = get_directory(temporary_directory.as_ref(), &cli)?;
    setup_teamtype_directory(&directory, temporary_directory.as_ref())
        .context("Failed to find .teamtype/ directory")?;

    // TODO: If the result of this joined future handles were to go out of scope and hence be
    // dropped, *some* but not all parts of the daemon would shut down. Notably the local socket
    // will go away but the remote networking connections would stay up! This is a fundamental issue
    // with the daemon module and merits refactoring so the long running socket and network
    // listeners properly listen to the mpsc channel or receive and process a cancellation token.
    let _handle = match cli.command {
        Commands::Client => return run_client(directory.clone()).await,
        Commands::Git { .. } => unreachable!("Handled before directory setup"),
        Commands::Tunnel { .. } => unreachable!("Handled before the directory setup"),
        Commands::AgentEdit {
            file,
            old,
            old_file,
            new,
            new_file,
            agent,
        } => {
            let [old, new] =
                [(old, old_file), (new, new_file)].map(|(text, path)| match (text, path) {
                    (Some(text), _) => Ok(text),
                    (None, Some(path)) => std::fs::read_to_string(&path)
                        .with_context(|| format!("Could not read {}", path.display())),
                    (None, None) => bail!("Missing content for the agent edit"),
                });
            agent_edit::prepare_snapshot(&directory, &agent, &file)?;
            let content = agent_edit::run(&directory, &file, &old?, &new?).await?;
            if let Err(error) =
                agent_edit::save_snapshot(&directory, &agent, &file, content.as_bytes())
            {
                eprintln!("Agent edit succeeded, but saving its snapshot failed: {error}");
            }
            return Ok(());
        }
        Commands::AgentRead { file, agent } => {
            return agent_edit::read(&directory, &agent, &file);
        }
        Commands::AgentDiff { file, agent } => {
            return agent_edit::diff(&directory, &agent, file.as_deref());
        }
        Commands::Join { .. } => {
            let join_config = parse_join_config(cli.command, directory.clone()).await?;
            confirm_overwrite(&join_config.base_dir)?;
            let marker = join_marker(&join_config.base_dir);
            let daemon = run_daemon(join_config, false).await?;
            // Only a join that connected counts, so that a failed one asks again.
            sandbox::write_file(&directory, &marker, b"")?;
            Ok(daemon)
        }
        Commands::Share { init, .. } => {
            let share_config = parse_share_config(cli.command, directory.clone());
            run_daemon(share_config, init).await
        }
    }?;

    trap_shutdown().await;

    Ok(())
}

async fn run_daemon(app_config: AppConfig, init_doc: bool) -> Result<Daemon> {
    // 🧑 "Prevent this bug in the future. Should likely prioritize server history"
    // Every peer keeps its history across restarts, so that the sharer's history continues and
    // joiners can tell whether theirs belongs to it; see `peer::sync`.
    let persist = true;

    config::ensure_teamtype_is_ignored(&app_config.base_dir)?;

    debug!("Starting TeamTypeV on {}.", app_config.base_dir.display());

    // Setup a new daemon from the derived config. Immediately join the handle because that's what
    // actually starts the local socket and any configured network connections. Return the result
    // so the calling context can determine when to terminate.
    Daemon::new(app_config, init_doc, persist)
        .await
        .context("Failed to launch the daemon")
}

async fn parse_join_config(command: Commands, directory: PathBuf) -> Result<AppConfig> {
    if let Commands::Join {
        join_code,
        shared_flags:
            ShareJoinFlags {
                magic_wormhole_relay,
                iroh_relay,
                iroh_dns_domain,
                iroh_pkarr_relay,
                no_sync_vcs,
                sync_vcs,
                username,
                ..
            },
        ..
    } = command
    {
        if no_sync_vcs || sync_vcs {
            warn!(
                "--sync-vcs and --no-sync-vcs are deprecated no-ops; Git commands run on the sharer"
            );
        }
        let app_config_cli = AppConfig {
            base_dir: directory,
            peer: join_code.map(config::Peer::JoinCode),
            emit_join_code: false,
            emit_secret_address: false,
            forward_port: None,
            magic_wormhole_relay,
            iroh_relay,
            iroh_dns_domain,
            iroh_pkarr_relay,
            username,
        };
        let mut app_config = AppConfig::from_config_file_and_cli(app_config_cli);
        app_config = app_config
            .resolve_peer()
            .await
            .context("Failed to resolve peer")?;
        Ok(app_config)
    } else {
        unreachable!("Only Join commands beget Join configs.")
    }
}

fn parse_share_config(command: Commands, directory: PathBuf) -> AppConfig {
    if let Commands::Share {
        no_join_code,
        shared_flags:
            ShareJoinFlags {
                magic_wormhole_relay,
                iroh_relay,
                iroh_dns_domain,
                iroh_pkarr_relay,
                no_sync_vcs,
                sync_vcs,
                username,
                ..
            },
        show_secret_address,
        forward_port,
        ..
    } = command
    {
        if no_sync_vcs || sync_vcs {
            warn!(
                "--sync-vcs and --no-sync-vcs are deprecated no-ops; Git commands run on the sharer"
            );
        }
        let app_config_cli = AppConfig {
            base_dir: directory,
            peer: None,
            emit_join_code: !no_join_code,
            emit_secret_address: show_secret_address,
            forward_port,
            magic_wormhole_relay,
            iroh_relay,
            iroh_dns_domain,
            iroh_pkarr_relay,
            username,
        };
        let mut app_config = AppConfig::from_config_file_and_cli(app_config_cli);
        // Because of the "share" subcommand, explicitly don't connect anywhere.
        app_config.peer = None;
        app_config
    } else {
        unreachable!("Only Share commands beget Share configs.")
    }
}

async fn run_client(directory: PathBuf) -> Result<()> {
    let jsonrpc_forwarder = UnixJSONRPCForwarder {};
    jsonrpc_forwarder
        .connection(&directory)
        .await
        .context("JSON-RPC forwarder failed")
}

async fn trap_shutdown() {
    let interruption = async {
        signal::ctrl_c()
            .await
            .expect("unable to setup Ctrl+C handler");
    };

    #[cfg(unix)]
    let termination = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("unable to setup SIGTERM handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let termination = std::future::pending::<()>();

    tokio::select! {
        () = interruption => {
            info!("Got SIGINT (Ctrl+C), shutting down");
        }
        () = termination => {
            info!("Got SIGTERM, shutting down");
        }
    }
}

fn get_temporary_directory(cli: &Cli) -> Result<Option<TempDir>> {
    match cli.command {
        Commands::Share {
            shared_flags:
                ShareJoinFlags {
                    temporary_directory,
                    ..
                },
            ..
        }
        | Commands::Join {
            shared_flags:
                ShareJoinFlags {
                    temporary_directory,
                    ..
                },
            ..
        } => {
            if temporary_directory {
                let temporary_directory_parent_directory = &get_app_cache_dir()?;
                Ok(Some(
                    tempdir_in(temporary_directory_parent_directory).with_context(|| {
                        format!(
                            "Failed to create a temporary directory in the directory {}",
                            temporary_directory_parent_directory.display()
                        )
                    })?,
                ))
            } else {
                Ok(None)
            }
        }
        Commands::Client
        | Commands::Git { .. }
        | Commands::Tunnel { .. }
        | Commands::AgentEdit { .. }
        | Commands::AgentRead { .. }
        | Commands::AgentDiff { .. } => Ok(None),
    }
}

fn get_app_cache_dir() -> Result<PathBuf> {
    let xdg = XdgApp::new("teamtype")?;
    let app_cache_dir = xdg.app_cache()?;
    let app_cache_dir_parent = app_cache_dir.parent().with_context(|| {
        format!(
            "Failed to get parent directory of the directory {}",
            app_cache_dir.display()
        )
    })?;
    // Using the sandbox method here is technically unnecessary,
    // but we want to really run all path operations through the sandbox module.
    sandbox::create_dir(app_cache_dir_parent, &app_cache_dir)?;
    Ok(app_cache_dir)
}

fn get_directory(temporary_directory: Option<&TempDir>, cli: &Cli) -> Result<PathBuf> {
    let directory = match temporary_directory {
        Some(temporary_directory) => &temporary_directory.path().to_path_buf(),
        None => match cli.directory {
            Some(ref directory) => directory,
            None => &get_current_directory()?,
        },
    };
    let directory = directory.canonicalize().with_context(|| {
        format!(
            "Could not compute the absolute, canonical form of the path of directory {}",
            directory.display(),
        )
    })?;
    Ok(directory)
}

fn setup_teamtype_directory(directory: &Path, temporary_directory: Option<&TempDir>) -> Result<()> {
    if has_ethersync_directory(directory) {
        let old_directory = directory.join(config::LEGACY_CONFIG_DIR);

        warn!(
            "You have an '{}/' directory, back from when the project was called \"Ethersync\" until October 2025.",
            &old_directory.display()
        );

        if prompt_bool(&format!(
            "Do you want to rename {}/ to {}/?",
            config::LEGACY_CONFIG_DIR,
            config::CONFIG_DIR,
        ))? {
            let new_directory = directory.join(config::CONFIG_DIR);
            sandbox::rename_file(directory, &old_directory, &new_directory)?;
        } else {
            bail!(
                "Aborting launch. Rename or remove the {} directory yourself to continue.",
                config::LEGACY_CONFIG_DIR
            );
        }
    }
    if !has_teamtype_directory(directory) {
        let teamtype_dir = directory.join(config::CONFIG_DIR);
        let directory_is_temporary_directory = temporary_directory.is_some();
        if directory_is_temporary_directory {
            info!(
                "'{}' is the temporary directory that is used as a TeamTypeV directory.",
                &directory.display()
            );
            sandbox::create_dir(directory, &teamtype_dir)?;
        } else {
            warn!(
                "'{}' hasn't been used as a TeamTypeV directory before.",
                &directory.display()
            );

            if prompt_bool(&format!(
                "Do you want to enable live collaboration here? (This will create an {}/ directory.)",
                config::CONFIG_DIR
            ))? {
                sandbox::create_dir(directory, &teamtype_dir)?;
                info!("Created! Resuming launch.");
            } else {
                bail!("Aborting launch. TeamTypeV needs a .teamtype/ directory to function");
            }
        }
    }
    Ok(())
}

// 🧑 "We should just upright refuse to connect if the user does not want the directory being
// overwritten ... So maybe we explicitly say that we will overwrite everything."
/// Joining replaces the directory's files with the sharer's versions. Asks before doing so to a
/// directory that has files and was not joined before.
fn confirm_overwrite(directory: &Path) -> Result<()> {
    let marker = join_marker(directory);
    let has_files = std::fs::read_dir(directory)?
        .flatten()
        .any(|entry| entry.file_name() != config::CONFIG_DIR);
    if has_files && !marker.exists() {
        warn!(
            "Joining overwrites the working files in '{}' with the sharer's versions.",
            directory.display()
        );
        if !prompt_bool("Overwrite them?")? {
            bail!("Aborting join. Join from an empty directory to keep your files");
        }
    } else {
        info!(
            "Joining keeps the working files here identical to the sharer's, overwriting local changes."
        );
    }
    Ok(())
}

fn join_marker(directory: &Path) -> PathBuf {
    directory.join(config::CONFIG_DIR).join("joined")
}

fn get_current_directory() -> Result<PathBuf> {
    env::current_dir().context("Could not access current directory")
}

fn prompt_bool(question: &str) -> Result<bool> {
    print!("{question} (y/N): ");
    stdout().flush()?;
    let mut lines = stdin().lines();
    if let Some(Ok(line)) = lines.next() {
        match line.to_lowercase().as_str() {
            "y" | "yes" => Ok(true),
            _ => Ok(false),
        }
    } else {
        bail!("Failed to read answer");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::{Command, Stdio};

    /// Runs the real stdin prompt in a separate test process so parallel tests cannot consume it.
    fn check_overwrite(
        directory: &Path,
        answer: &str,
        expected: &str,
        prompts: bool,
    ) -> Result<()> {
        let mut child = Command::new(env::current_exe()?)
            .args(["--exact", "tests::overwrite_prompt_child", "--nocapture"])
            .env("TEAMTYPE_TEST_OVERWRITE_DIR", directory)
            .env("TEAMTYPE_TEST_OVERWRITE_RESULT", expected)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        child
            .stdin
            .take()
            .expect("piped stdin")
            .write_all(answer.as_bytes())?;
        let output = child.wait_with_output()?;
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout).contains("Overwrite them? (y/N):"),
            prompts
        );
        Ok(())
    }

    #[test]
    fn overwrite_prompt_child() -> Result<()> {
        let Some(directory) = env::var_os("TEAMTYPE_TEST_OVERWRITE_DIR") else {
            return Ok(());
        };
        let expected = env::var("TEAMTYPE_TEST_OVERWRITE_RESULT")?;
        let result = confirm_overwrite(Path::new(&directory));
        if expected == "ok" {
            result?;
        } else {
            assert!(
                result
                    .expect_err("join must be refused")
                    .to_string()
                    .contains(&expected)
            );
        }
        Ok(())
    }

    #[test]
    fn overwrite_confirmation_skips_empty_config_only_and_previously_joined_directories()
    -> Result<()> {
        let dir = tempfile::tempdir()?;
        check_overwrite(dir.path(), "", "ok", false)?;
        std::fs::create_dir(dir.path().join(config::CONFIG_DIR))?;
        std::fs::write(
            dir.path().join(config::CONFIG_DIR).join("config"),
            "configuration",
        )?;
        check_overwrite(dir.path(), "", "ok", false)?;
        std::fs::write(dir.path().join("local.txt"), "keep me")?;
        std::fs::write(join_marker(dir.path()), "")?;
        check_overwrite(dir.path(), "", "ok", false)?;
        assert_eq!(
            std::fs::read_to_string(dir.path().join("local.txt"))?,
            "keep me"
        );
        Ok(())
    }

    #[test]
    fn overwrite_confirmation_requires_explicit_yes_and_never_marks_the_join() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::create_dir(dir.path().join(config::CONFIG_DIR))?;
        let local = dir.path().join("local.txt");
        std::fs::write(&local, "keep me")?;
        for answer in ["n\n", "\n", "maybe\n", " yes\n"] {
            check_overwrite(dir.path(), answer, "Aborting join", true)?;
        }
        check_overwrite(dir.path(), "", "Failed to read answer", true)?;
        for answer in ["y\n", "yes\n", "Y\n", "YES\n"] {
            check_overwrite(dir.path(), answer, "ok", true)?;
        }
        assert!(!join_marker(dir.path()).exists());
        assert_eq!(std::fs::read_to_string(local)?, "keep me");
        Ok(())
    }

    #[test]
    fn overwrite_confirmation_protects_git_only_directories() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::create_dir(dir.path().join(".git"))?;
        check_overwrite(dir.path(), "n\n", "Aborting join", true)?;
        check_overwrite(dir.path(), "yes\n", "ok", true)?;
        Ok(())
    }
}
