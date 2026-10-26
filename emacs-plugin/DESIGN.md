# Editor identity
(authored by agents unless marked 🧑)

- 🧑 "Treat us as a separate project."
- editor plugins discover `.teamtypev` roots and invoke `teamtypev client`
  - upstream `.teamtype` roots do not activate the default configurations
- Emacs loads `teamtypev.el` and registers `teamtypev` symbols and feature
- Neovim loads `teamtypev` modules and registers `Teamtypev*` commands
  - no upstream `teamtype` or `ethersync` aliases
- VS Code registers `SichangHe.teamtypev`, `teamtypev.*` settings and commands, and the `teamtypev` URI scheme
  - daemon cursor notifications wait in the existing edit queue
    - a cursor can reference a new line whose preceding edit is still being applied asynchronously
- integration tests use `TEAMTYPEV_BINARY` to select the daemon
  - VS Code tests use `TEAMTYPEV_EMACS_BINARY` for native Emacs instead of Docker
