# Upgrading an existing fork installation
(authored by agents unless marked 🧑)

TeamTypeV now uses `teamtypev`, `.teamtypev`, `.teamtypevignore`, and `TEAMTYPEV_*` environment variables. Its editor plugins also use `teamtypev`; the VS Code extension ID is `SichangHe.teamtypev`. These names are separate from upstream Teamtype. New installations can follow [Getting started](getting-started.md).

There is no automatic migration from `.teamtype` or `.ethersync`. Only move state that you know was created by an earlier **TeamTypeV fork** installation. Leave upstream Teamtype directories, ignore files, executable, and plugins in place if you still use upstream. Use separate working directories for the two projects.

For an existing fork project, upgrade offline on every peer:

1. Stop the old sharing/joining daemon and close its editor clients. Back up the whole project, including hidden files and the old `.teamtype` directory.
2. Confirm that `.teamtype` belongs to the fork and that `.teamtypev` does not already exist. Rename that `.teamtype` directory to `.teamtypev`. Preserve its `key`, `doc`, and configuration; do not create a fresh history or overwrite another state directory.
3. Rename the fork's `.teamtypeignore` files to `.teamtypevignore`, including any in subdirectories. Update project ignore rules and scripts that refer to the old names. Do not rename upstream ignore files in projects you intend to keep using with upstream.
4. Install the new executable and plugins on every peer. Remove the earlier fork plugin's init/config entries or installation so it cannot attach to old `.teamtype` projects. Keep genuine upstream plugins if wanted. Update custom commands, settings, and environment variables to the new names.
5. Start `teamtypev share` on the sharer, then `teamtypev join` on existing joiners. Restart editors and open files only after their local daemon is running. If you use Git activation, deactivate the old shell environment and source the newly generated `.teamtypev/activate` or `.teamtypev/activate.fish`.

Keep the backup until you have checked file contents and edits between peers. If you cannot establish whether old state belongs to the fork, leave it untouched and start a separate TeamTypeV project from a copy of the working files.
