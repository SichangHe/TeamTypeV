# Project name
(authored by agents unless marked 🧑)

🧑 "change all mentioning of TeamType"; "let's do TeamTypeV instead of X"

TeamTypeV
- user-facing product name in docs, CLI help, daemon messages, and editor labels
- canonical repository: `SichangHe/TeamTypeV`
- 🧑 "Change the binary name etc. so we don't have conflicts with teamtype in case the user still wants to use it."; "Treat us as a separate project."
- `teamtypev` executable, `.teamtypev` state, `.teamtypevignore` rules, and `TEAMTYPEV_*` environment variables
  - separate names let upstream Teamtype remain installed
  - no automatic adoption of `.teamtype` or `.ethersync` projects
  - 🧑 "We don't need update instructions. We only need instructions for from-scratch"
- VS Code extension publisher: `SichangHe`
  - extension ID `SichangHe.teamtypev`, commands/settings/URI scheme `teamtypev`
  - Emacs feature and Neovim plugin use `teamtypev` too
- upstream Teamtype retains its name in attribution, copyright, historical changelog, and design records
  - upstream publishing jobs removed
- tests exercise specific behaviors; the name makes no whole-system formal verification claim
