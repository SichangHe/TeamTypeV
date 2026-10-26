-- SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
-- SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>
-- SPDX-FileCopyrightText: 2026 Caleb Maclennan <caleb@alerque.com>
--
-- SPDX-License-Identifier: AGPL-3.0-or-later

-- 🧑 "Treat us as a separate project."
local teamtypev = require("teamtypev")

-- Enable testing or using a teamtypev binary outside of the path without
-- creating a dedicated config file for it. Used in e2e testing.
local binary_name = os.getenv("TEAMTYPEV_BINARY") or "teamtypev"

teamtypev.config("teamtypev", {
    cmd = { binary_name, "client" },
    root_markers = ".teamtypev",
})

teamtypev.enable("teamtypev")
