<!--
SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>

SPDX-License-Identifier: CC-BY-SA-4.0
-->

# VS Code plugin for 🍃 [TeamTypeV](https://github.com/SichangHe/TeamTypeV)-compatible projects
(authored by agents unless marked 🧑)

Note: You will need to install and run a "collaboration server" like TeamTypeV in addition to this plugin!

Refer to the [main project](https://github.com/SichangHe/TeamTypeV) for documentation and usage instructions.

Install the plugin from this checkout using the [local installation instructions](DEVELOPMENT.md#how-to-run-locally-without-host). The upstream marketplace extension does not contain TeamTypeV's changes.

The local extension ID is `SichangHe.teamtype`. Disable the upstream `teamtype.teamtype` extension before loading it to avoid two plugins handling the same files. The `teamtype.*` settings and commands remain compatible.

## Configuration

A configuration for connecting to TeamTypeV daemons is provided as a default value.

You can also use this plugin with other collaboration servers.

To add other configurations, add a section like this to your `settings.json` (you can access it using *F1 -> Preferences: Open User Settings (JSON)*):

```jsonc
"teamtype.configs": {
  /* Default configuration */
  "teamtype": {
    "cmd": [ "teamtype", "client" ],
    "rootMarkers": [ ".teamtype" ]
   },

  /* Hypothetical configuration for another program */
  "http": {
    "cmd": [ "teamtype-http" ],
    "rootMarkers": [ ".teamtype-http" ]
  },
}
```

Available options:

- `cmd`: Array of strings to specify the command to be launched to connect to the collaboration server.
- `rootMarkers`: Array of strings to indicate if a directory should be considered as a collaboration project for this configuration.
