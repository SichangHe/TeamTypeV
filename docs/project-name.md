# Project name
(authored by agents unless marked 🧑)

🧑 "change all mentioning of TeamType"; "let's do TeamTypeV instead of X"

TeamTypeV
- user-facing product name in docs, CLI help, daemon messages, and editor labels
- canonical repository: `SichangHe/TeamTypeV`
- `teamtype` executable, crate, protocol, settings, and `.teamtype` paths remain compatible
  - installation docs identify these as compatibility names
- VS Code extension publisher: `SichangHe`
  - disables confusion with upstream's `teamtype.teamtype` identity
  - users must disable the upstream extension before loading this one
- upstream Teamtype retains its name in attribution, copyright, historical changelog, and design records
  - upstream publishing jobs removed
- tests exercise specific behaviors; the name makes no whole-system formal verification claim
