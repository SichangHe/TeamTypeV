// SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>
// SPDX-FileCopyrightText: 2026 axelmartensson <axel.martensson@hotmail.com>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

use std::path::PathBuf;

use clap::{Args, Parser, Subcommand};

// TODO: Define these constants in the teamtype crate, and use them here.
#[derive(Parser)]
#[command(about, long_about = None)]
#[command(propagate_version = true)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
    /// The shared directory. Defaults to current directory.
    #[arg(long, global = true)]
    pub directory: Option<PathBuf>,
}

#[derive(Args)]
pub struct ShareJoinFlags {
    /// EXPERIMENTAL: Also synchronize version-control directories like .git/ or .jj/, which are normally
    /// ignored. For Git, this will synchronize all branches, commits, etc. as well as your .git/config.
    /// This means that new commits will immediately appear at all peers, you can change branches together, etc.
    #[arg(long)]
    pub sync_vcs: bool,
    /// Use an alternative Magic Wormhole mailbox server relay url
    #[arg(long)]
    pub magic_wormhole_relay: Option<String>,
    /// Use an alternative Iroh relay url
    #[arg(long)]
    pub iroh_relay: Option<String>,
    /// Use an alternative Iroh DNS origin domain.
    #[arg(long)]
    pub iroh_dns_domain: Option<String>,
    /// Use an alternative Iroh Pkarr relay server.
    #[arg(long)]
    pub iroh_pkarr_relay: Option<String>,
    #[arg(long)]
    /// The name that others see next to your cursor. Defaults to your Git username.
    pub username: Option<String>,
    /// Create a new temporary directory and use it as the shared directory.
    /// The temporary directory is removed on exit.
    /// The temporary directory is created in `$XDG_CACHE_DIR/teamtype/`,
    /// or if `XDG_CACHE_DIR` is not set in `$HOME/.cache/teamtype/`,
    /// or if `HOME` is not set in `/home/$USER/.cache/teamtype/`.
    #[arg(short, long)]
    pub temporary_directory: bool,
}

#[derive(Subcommand)]
pub enum Commands {
    /// Share a directory with a new peer.
    Share {
        /// Re-initialize the history of the shared directory. You will loose previous history.
        #[arg(long)]
        init: bool,
        /// Do not generate a join code. To prevent unintended sharing or simply if you want to
        /// keep Magic Wormhole out of the loop.
        #[arg(long)]
        no_join_code: bool,
        /// Print the secret address. Useful for sharing with multiple people.
        #[arg(long)]
        show_secret_address: bool,
        #[command(flatten)]
        shared_flags: ShareJoinFlags,
    },
    /// Join a shared directory via a join code, or connect to the most recent one.
    Join {
        /// Specify to connect to a new peer. Otherwise, try to connect to the most recent peer.
        join_code: Option<String>,
        #[command(flatten)]
        shared_flags: ShareJoinFlags,
    },
    /// Open a JSON-RPC connection to the Teamtype daemon on stdin/stdout. Used by text editor plugins.
    Client,
    /// Replace one exact piece of text in a file through the running daemon. For command line
    /// tools such as coding agents.
    ///
    /// Use this instead of writing a shared file directly: the daemon ignores disk writes to files
    /// open in an editor, and a direct write can undo other people's edits.
    ///
    /// How it works: teamtype reads the file's current content itself, requires `--old` to occur
    /// in it exactly once, and replaces only that occurrence with `--new`. Text outside `--old` is
    /// never touched, so the edit cannot revert changes others made elsewhere, even if the caller's
    /// own copy of the file is stale. If someone changed the text inside `--old`, the edit is
    /// rejected and nothing changes.
    ///
    /// Recipe:
    ///   1. Read the file.
    ///   2. Pick the smallest piece of text you want to change, plus enough surrounding text to
    ///      make it unique; pass it as `--old`, and its new version as `--new`.
    ///   3. If rejected, read the file again and redo step 2. Never reuse `--old`/`--new` files
    ///      left over from an earlier attempt.
    ///
    /// Make one call per change rather than replacing the whole file: a whole-file `--old` is
    /// rejected as soon as anyone edits anything.
    ///
    /// Example:
    ///   teamtype agent-edit --file notes.md --old 'teh cat' --new 'the cat'
    #[command(verbatim_doc_comment)]
    AgentEdit {
        /// File path relative to the shared directory.
        #[arg(long)]
        file: PathBuf,
        /// Exact text to replace; it must occur exactly once in the file.
        #[arg(long, required_unless_present = "old_file")]
        old: Option<String>,
        /// File holding the text to replace, for text too large for an argument.
        #[arg(long, conflicts_with = "old")]
        old_file: Option<PathBuf>,
        /// Text to put in its place.
        #[arg(long, required_unless_present = "new_file")]
        new: Option<String>,
        /// File holding the text to put in its place.
        #[arg(long, conflicts_with = "new")]
        new_file: Option<PathBuf>,
    },
}
