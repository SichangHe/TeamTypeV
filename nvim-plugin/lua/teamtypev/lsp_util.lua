-- SPDX-FileCopyrightText: 2019 Neovim contributors
--
-- SPDX-License-Identifier: Apache-2.0

local M = {}

-- These functions are taken from the Neovim source code:
-- https://github.com/neovim/neovim/blob/master/runtime/lua/vim/lsp/util.lua

local function nchars(s)
    return vim.fn.strchars(s)
end

-- Byte index (0-based) of the 0-based character index `ci` in `s`. Requires ci <= nchars(s).
-- Characters are Unicode scalar values, as the daemon counts them.
local function byte_index(s, ci)
    local n, i = 0, 1
    while n < ci do
        i = i + 1
        while i <= #s and s:byte(i) >= 0x80 and s:byte(i) < 0xC0 do
            i = i + 1
        end
        n = n + 1
    end
    return i - 1
end

--- Applies a list of text edits (all positions refer to the text before any edit), as the daemon sends them.
---
--- Positions are (line, character) in "logical" text: the buffer lines joined by "\n", plus one more
--- empty line if 'eol' is on (see docs/decisions/02-working-with-vims-eol-behavior.md). `character` counts
--- Unicode scalar values.
---
--- All edits are validated first. If they are not all valid, or applying throws, the buffer is left as it was
--- and `false, reason` is returned. Otherwise returns `true`.
---
--- Afterwards the buffer is in canonical form: 'eol' is on iff the logical text has at least two logical
--- lines and ends with "\n". The logical text is exactly what the edits describe.
---@param text_edits table list of `TextEdit` objects
---@param bufnr integer Buffer id
---@param offset_encoding string must be "utf-32"
---@return boolean ok
---@return string? reason
function M.apply_text_edits(text_edits, bufnr, offset_encoding)
    vim.validate({
        text_edits = { text_edits, "t", false },
        bufnr = { bufnr, "number", false },
        offset_encoding = { offset_encoding, "string", false },
    })
    if offset_encoding ~= "utf-32" then
        return false, "only utf-32 offsets are supported"
    end
    if not next(text_edits) then
        return true
    end
    if not vim.api.nvim_buf_is_loaded(bufnr) then
        return false, "buffer is not loaded"
    end
    if not vim.bo[bufnr].modifiable then
        return false, "buffer is not modifiable"
    end

    local orig_lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, true)
    local orig_eol = vim.bo[bufnr].eol
    local logical = vim.list_extend({}, orig_lines)
    if orig_eol then
        table.insert(logical, "")
    end

    -- Validate, normalize reversed ranges, and index.
    local edits = {}
    for index, text_edit in ipairs(text_edits) do
        local s, e = text_edit.range.start, text_edit.range["end"]
        if s.line > e.line or (s.line == e.line and s.character > e.character) then
            s, e = e, s
        end
        for _, p in ipairs({ s, e }) do
            local line = logical[p.line + 1]
            if p.line < 0 or line == nil or p.character < 0 or p.character > nchars(line) then
                return false, "position out of range"
            end
        end
        table.insert(edits, {
            index = index,
            start_line = s.line,
            start_char = s.character,
            end_line = e.line,
            end_char = e.character,
            text = (string.gsub(text_edit.newText, "\r\n?", "\n")),
        })
    end

    -- Order by position (ascending) and check that edits do not overlap.
    table.sort(edits, function(a, b)
        if a.start_line ~= b.start_line then
            return a.start_line < b.start_line
        end
        if a.start_char ~= b.start_char then
            return a.start_char < b.start_char
        end
        if a.end_line ~= b.end_line then
            return a.end_line < b.end_line
        end
        if a.end_char ~= b.end_char then
            return a.end_char < b.end_char
        end
        return a.index < b.index
    end)
    for i = 2, #edits do
        local prev, cur = edits[i - 1], edits[i]
        if prev.end_line > cur.start_line or (prev.end_line == cur.start_line and prev.end_char > cur.start_char) then
            return false, "overlapping edits"
        end
    end

    local function restore()
        vim.bo[bufnr].eol = orig_eol
        vim.api.nvim_buf_set_lines(bufnr, 0, -1, true, orig_lines)
    end

    local ok, err = pcall(function()
        -- Make the implicit final newline explicit, so that every logical position is a buffer position.
        -- (First clear 'eol', then add the line: the last change notification then sees consistent state.)
        if orig_eol then
            vim.bo[bufnr].eol = false
            vim.api.nvim_buf_set_lines(bufnr, #orig_lines, #orig_lines, true, { "" })
        end

        -- Apply from the end, so earlier positions stay valid.
        for i = #edits, 1, -1 do
            local e = edits[i]
            local start_text = vim.api.nvim_buf_get_lines(bufnr, e.start_line, e.start_line + 1, true)[1]
            local end_text = vim.api.nvim_buf_get_lines(bufnr, e.end_line, e.end_line + 1, true)[1]
            vim.api.nvim_buf_set_text(
                bufnr,
                e.start_line,
                byte_index(start_text, e.start_char),
                e.end_line,
                byte_index(end_text, e.end_char),
                vim.split(e.text, "\n", { plain = true })
            )
        end

        -- Back to canonical form: a final empty line (of at least two) becomes the implicit newline.
        -- (First set 'eol', then remove the line, for the same reason as above.)
        local n = vim.api.nvim_buf_line_count(bufnr)
        if n >= 2 and vim.api.nvim_buf_get_lines(bufnr, n - 1, n, true)[1] == "" then
            vim.bo[bufnr].eol = true
            vim.api.nvim_buf_set_lines(bufnr, n - 1, n, true, {})
        end
    end)
    if not ok then
        pcall(restore)
        return false, tostring(err)
    end
    return true
end

return M
