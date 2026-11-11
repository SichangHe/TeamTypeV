-- SPDX-FileCopyrightText: 2026 TeamTypeV contributors
--
-- SPDX-License-Identifier: AGPL-3.0-or-later

-- Headless tests of the editor side of the daemon-editor protocol, without a daemon.
-- Run from the nvim-plugin directory: nvim --headless -u NONE -l test/run.lua
vim.opt.rtp:prepend(vim.fn.getcwd())
local changetracker = require("teamtypev.changetracker")
local plugin = require("teamtypev")

local failures = 0
local function check(cond, msg)
    if not cond then
        failures = failures + 1
        print("FAIL: " .. msg)
    end
end

local function logical(buf)
    return table.concat(changetracker.get_all_lines_respecting_eol(buf), "\n")
end

local function new_buf(content)
    local buf = vim.api.nvim_create_buf(true, false)
    vim.api.nvim_set_current_buf(buf)
    local lines, eol
    if content == "" then
        lines, eol = { "" }, false
    elseif content:sub(-1) == "\n" then
        lines, eol = vim.split(content:sub(1, -2), "\n", { plain = true }), true
    else
        lines, eol = vim.split(content, "\n", { plain = true }), false
    end
    vim.api.nvim_buf_set_lines(buf, 0, -1, true, lines)
    vim.bo[buf].eol = eol
    return buf
end

-- Reference semantics (the daemon's): positions are (line, char) in characters; lines end at "\n".
local function chars(s)
    return vim.fn.strchars(s)
end
local function offset(text, pos)
    local off = 0
    local lines = vim.split(text, "\n", { plain = true })
    assert(pos.line < #lines and pos.character <= chars(lines[pos.line + 1]), "invalid position")
    for i = 1, pos.line do
        off = off + chars(lines[i]) + 1
    end
    return off + pos.character
end
local function sub_chars(s, from, to) -- 0-based [from, to)
    return vim.fn.strcharpart(s, from, to - from)
end
local function apply(text, op)
    local s, e = offset(text, op.range.start), offset(text, op.range["end"])
    return sub_chars(text, 0, s) .. op.replacement .. sub_chars(text, e, chars(text))
end

local function edit(sl, sc, el, ec, text)
    return {
        range = { start = { line = sl, character = sc }, ["end"] = { line = el, character = ec } },
        replacement = text,
    }
end

-- Track a buffer, collecting emitted deltas.
local function track(buf)
    local emitted = {}
    changetracker.track_changes(buf, changetracker.get_all_lines_respecting_eol(buf), function(d)
        table.insert(emitted, d)
    end)
    return emitted
end

-- 1. apply_delta: results, eol convention, no echo.
local apply_cases = {
    -- content, edit, expected content
    { "a\n", edit(1, 0, 1, 0, "x"), "a\nx" },
    { "a\n", edit(0, 1, 0, 1, "b"), "ab\n" },
    { "a\n", edit(0, 1, 1, 0, ""), "a" },
    { "a\n", edit(0, 0, 1, 0, ""), "" },
    { "a\n", edit(0, 0, 0, 1, ""), "\n" },
    { "a", edit(0, 1, 0, 1, "\n"), "a\n" },
    { "a\n\n", edit(1, 0, 2, 0, ""), "a\n" },
    { "", edit(0, 0, 0, 0, "x\n"), "x\n" },
    { "", edit(0, 0, 0, 0, "\n"), "\n" },
    { "\n", edit(0, 0, 1, 0, ""), "" },
    { "\u{1F600}e\u{301}\n", edit(0, 1, 0, 2, "z"), "\u{1F600}z\u{301}\n" },
    { "\u{65e5}\u{1F600}b\n", edit(0, 2, 0, 3, "\n"), "\u{65e5}\u{1F600}\n\n" },
}
for i, c in ipairs(apply_cases) do
    local buf = new_buf(c[1])
    local emitted = track(buf)
    local ok = changetracker.apply_delta(buf, { c[2] })
    check(ok, "apply case " .. i .. " reported failure")
    check(logical(buf) == c[3], ("apply case %d: expected %q got %q"):format(i, c[3], logical(buf)))
    check(#emitted == 0, "apply case " .. i .. " echoed a delta")
end

-- 2. A delta that cannot be applied leaves the buffer alone, reports failure, and does not
-- stop later local edits from being reported (ignore_edits must not stay set).
do
    local buf = new_buf("ab\ncd\n")
    local emitted = track(buf)
    local bad = {
        { edit(5, 0, 5, 0, "x") },
        { edit(0, 9, 0, 9, "x") },
        { edit(0, 0, 0, 1, "x"), edit(0, 0, 0, 2, "y") }, -- overlapping
        { edit(0, 0, 2, 1, "x") }, -- past the implicit final newline
    }
    for i, delta in ipairs(bad) do
        local ok, reason = changetracker.apply_delta(buf, delta)
        check(ok == false and reason ~= nil, "bad delta " .. i .. " must report failure")
        check(logical(buf) == "ab\ncd\n", "bad delta " .. i .. " must not change the buffer")
    end
    vim.api.nvim_buf_set_text(buf, 0, 0, 0, 0, { "z" })
    check(#emitted == 1 and emitted[1][1].replacement == "z", "local edit after failed apply must be reported")
end

-- 3. Random local edits: emitted deltas folded over the initial text equal the buffer.
do
    local pieces = { "a", "b", " ", "\u{e9}", "\u{65e5}", "\u{1F600}", "e\u{301}", "\n", "\n" }
    local cmds =
        { "dd", "x", "p", "P", "u", "ddp", "J", "yyp", "ggdG", "Gdd", "ggdd", "dG", "oab\27", "Ox\27", "A\u{e9}\27" }
    math.randomseed(12345)
    local failed
    for seed = 1, 300 do
        math.randomseed(seed)
        local t = {}
        for _ = 1, math.random(0, 8) do
            t[#t + 1] = pieces[math.random(#pieces)]
        end
        local init = table.concat(t)
        local buf = new_buf(init)
        local emitted = track(buf)
        local text = logical(buf)
        for step = 1, 8 do
            for k = #emitted, 1, -1 do
                emitted[k] = nil
            end
            local before = logical(buf)
            local what
            if math.random(3) == 1 then
                what = "normal"
                local cmd = cmds[math.random(#cmds)]
                vim.api.nvim_win_set_cursor(0, { 1, 0 })
                pcall(vim.cmd, "silent normal! " .. cmd)
            else
                what = "set_lines"
                local n = vim.api.nvim_buf_line_count(buf)
                local a = math.random(0, n)
                local b = math.random(a, n)
                local rep = {}
                for _ = 1, math.random(0, 2) do
                    rep[#rep + 1] = pieces[math.random(#pieces)]:gsub("\n", "")
                end
                vim.api.nvim_buf_set_lines(buf, a, b, true, rep)
            end
            text = before
            local ok = pcall(function()
                for _, d in ipairs(emitted) do
                    check(#d == 1, "one op per delta")
                    text = apply(text, d[1])
                end
            end)
            if not ok or text ~= logical(buf) then
                failed = failed
                    or ("seed %d step %d (%s): folded %q, buffer %q"):format(
                        seed,
                        step,
                        what,
                        tostring(text),
                        logical(buf)
                    )
            end
        end
    end
    check(failed == nil, failed or "")
end

-- 4. process_operation_for_editor (revision rules, rejection, closed files).
do
    local sent = {}
    local client = {
        files = {},
        buffers = {},
        connection = {
            send_request = function(_, method, params)
                if method == "edit" then
                    table.insert(sent, { method, params })
                end
            end,
        },
    }
    local buf = new_buf("ab\n")
    vim.api.nvim_buf_set_name(buf, vim.fn.tempname())
    local uri = vim.uri_from_bufnr(buf)
    plugin._internal.track_edits(client, buf, uri, changetracker.get_all_lines_respecting_eol(buf))
    local state = client.files[buf]
    local process = plugin._internal.process_operation_for_editor

    -- own edit: sent with revision = daemon_revision, then editor_revision += 1
    vim.api.nvim_buf_set_text(buf, 0, 0, 0, 0, { "x" })
    check(#sent == 1 and sent[1][2].revision == 0 and state.editor_revision == 1, "own edit sent with daemon revision")

    -- daemon edit with a stale revision is ignored
    process(client, "edit", { uri = uri, revision = 0, delta = { edit(0, 0, 0, 0, "STALE") } })
    check(logical(buf) == "xab\n" and state.daemon_revision == 0, "stale daemon edit must be ignored")

    -- matching revision is applied, daemon_revision += 1, nothing echoed
    process(client, "edit", { uri = uri, revision = 1, delta = { edit(0, 0, 0, 0, "D") } })
    check(logical(buf) == "Dxab\n" and state.daemon_revision == 1 and #sent == 1, "daemon edit applied without echo")

    -- an edit that cannot be applied: empty delta with revision = daemon_revision; editor_revision += 1
    local err_write = vim.api.nvim_err_writeln
    vim.api.nvim_err_writeln = function() end
    process(client, "edit", { uri = uri, revision = 1, delta = { edit(9, 0, 9, 0, "BAD") } })
    vim.api.nvim_err_writeln = err_write
    check(logical(buf) == "Dxab\n", "rejected edit must not change the buffer")
    check(
        #sent == 2 and sent[2][1] == "edit" and #sent[2][2].delta == 0 and sent[2][2].revision == 1,
        "rejected edit must be answered with an empty delta at the daemon revision"
    )
    check(state.editor_revision == 2 and state.daemon_revision == 1, "rejection counts as an own operation only")

    -- local editing still works afterwards
    vim.api.nvim_buf_set_text(buf, 0, 0, 0, 0, { "y" })
    check(#sent == 3 and sent[3][2].revision == 1, "local edit after rejection is sent")

    -- edits for a file with no synced state (not opened yet, or closed) must not raise
    local before = #sent
    local ok = pcall(
        process,
        client,
        "edit",
        { uri = "file:///no/such/file", revision = 0, delta = { edit(0, 0, 0, 0, "q") } }
    )
    check(ok, "edit for an unknown file must not raise")
    client.files[buf] = nil
    ok = pcall(process, client, "edit", { uri = uri, revision = 0, delta = { edit(0, 0, 0, 0, "q") } })
    check(ok and logical(buf) == "yDxab\n" and #sent == before, "edit after close must be dropped")

    -- callbacks of a closed (or reopened) session do not send
    vim.api.nvim_buf_set_text(buf, 0, 0, 0, 0, { "w" })
    check(#sent == before, "edits after close must not be sent")
end

-- 5. The answer to an old `open` (closed and reopened meanwhile) must not start the new session.
do
    local client = { files = {}, buffers = {}, sessions = {}, connection = { send_request = function() end } }
    local buf = new_buf("ab\n")
    vim.api.nvim_buf_set_name(buf, vim.fn.tempname())
    local uri = vim.uri_from_bufnr(buf)
    local lines = changetracker.get_all_lines_respecting_eol(buf)
    local on_answer = plugin._internal.on_open_answer
    local old, new = {}, {}
    table.insert(client.buffers, buf)
    client.sessions[buf] = old
    -- close, then reopen: a new session token, the old answer still to come
    client.sessions[buf] = new
    on_answer(client, buf, uri, lines, old)
    check(client.files[buf] == nil, "answer of an old open must not start the session")
    on_answer(client, buf, uri, lines, new)
    check(client.files[buf] ~= nil, "answer of the current open starts the session")
    client.sessions[buf] = nil
    client.files[buf] = nil
    on_answer(client, buf, uri, lines, new)
    check(client.files[buf] == nil, "answer after close must not start a session")
end

-- 6. Randomized protocol scenarios against a reference state machine of the rules (the model proved in
-- editor_proof): events are local edits, daemon edits with arbitrary revisions (fitting or not), close,
-- reopen, and answers to current and stale open requests, in random order.
do
    local sent
    local client = {
        files = {},
        buffers = {},
        sessions = {},
        connection = {
            send_request = function(_, method, params)
                if method == "edit" then
                    table.insert(sent, params)
                end
            end,
        },
    }
    local err_write = vim.api.nvim_err_writeln
    vim.api.nvim_err_writeln = function() end
    local process = plugin._internal.process_operation_for_editor
    local answer = plugin._internal.on_open_answer
    for seed = 1, 200 do
        math.randomseed(seed)
        local buf = new_buf("abc\ndef\n")
        vim.api.nvim_buf_set_name(buf, vim.fn.tempname())
        local uri = vim.uri_from_bufnr(buf)
        client.files, client.sessions, client.buffers = {}, {}, { buf }
        sent = {}
        local o = { live = false, dr = 0, er = 0, sent = 0 } -- oracle
        local tokens, pending = {}, nil
        local function snapshot()
            return changetracker.get_all_lines_respecting_eol(buf)
        end
        local function open()
            local tok = {}
            client.sessions[buf] = tok
            tokens[#tokens + 1] = tok
            pending = tok
            o.live = false
            client.files[buf] = nil
        end
        local function close()
            client.files[buf] = nil
            client.sessions[buf] = nil
            pending, o.live = nil, false
        end
        open()
        for step = 1, 40 do
            local kind = math.random(1, 7)
            local ctx = "seed " .. seed .. " step " .. step .. " kind " .. kind
            if kind == 1 then -- answer to the current or a stale open
                -- each request is answered at most once
                local ti = math.random(1, math.max(#tokens, 1))
                local tok = table.remove(tokens, ti) or {}
                answer(client, buf, uri, snapshot(), tok)
                if tok == pending and pending ~= nil then
                    o = { live = true, dr = 0, er = 0, sent = #sent }
                    pending = nil
                end
            elseif kind == 2 then
                close()
            elseif kind == 3 then
                if client.sessions[buf] == nil or math.random(1, 2) == 1 then
                    open()
                end
            elseif kind == 4 then -- local edit
                local n = #sent
                vim.api.nvim_buf_set_text(buf, 0, 0, 0, 0, { "x" })
                if o.live then
                    check(
                        #sent == n + 1 and sent[#sent].revision == o.dr and #sent[#sent].delta == 1,
                        ctx .. " local edit sent"
                    )
                    o.er = o.er + 1
                else
                    check(#sent == n, ctx .. " local edit outside a session must not be sent")
                end
            else -- daemon edit
                local revs = { o.er, o.er, o.er - 1, o.er + 1, 0 }
                local rev = revs[math.random(1, #revs)]
                local fits = math.random(1, 3) > 1
                local d = fits and edit(0, 0, 0, 0, "D") or edit(40, 0, 40, 0, "BAD")
                local before, n = logical(buf), #sent
                process(client, "edit", { uri = uri, revision = rev, delta = { d } })
                if o.live and rev == o.er then
                    if fits then
                        check(logical(buf) == "D" .. before and #sent == n, ctx .. " daemon edit applied")
                        o.dr = o.dr + 1
                    else
                        check(logical(buf) == before, ctx .. " rejected edit changes nothing")
                        check(
                            #sent == n + 1 and #sent[#sent].delta == 0 and sent[#sent].revision == o.dr,
                            ctx .. " rejection answered with an empty delta at the daemon revision"
                        )
                        o.er = o.er + 1
                    end
                else
                    check(logical(buf) == before and #sent == n, ctx .. " stale or sessionless edit ignored")
                end
            end
            if o.live then
                local st = client.files[buf]
                check(st ~= nil and st.daemon_revision == o.dr and st.editor_revision == o.er, ctx .. " revisions")
            else
                check(client.files[buf] == nil, ctx .. " no session state")
            end
        end
    end
    vim.api.nvim_err_writeln = err_write
end

if failures > 0 then
    print(failures .. " check(s) failed")
    vim.cmd("cquit 1")
end
print("ok")
vim.cmd("qa!")
