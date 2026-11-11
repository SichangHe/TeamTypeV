// SPDX-License-Identifier: AGPL-3.0-or-later
// Differential test: the REAL position conversions of src/extension.ts against an independent
// Python reference (position_reference.py), and editor-vs-daemon line agreement.
const assert = require("node:assert/strict")
const {execFileSync} = require("node:child_process")
const path = require("node:path")
const {loadReal} = require("./real.cjs")

class Position { constructor(line, character) { this.line = line; this.character = character } }
const {fns} = loadReal(
    ["UTF16CodeUnitOffsetToCharOffset", "charOffsetToUTF16CodeUnitOffset", "isHighSurrogate", "isLowSurrogate",
     "vsCodePositionToTeamtypevPosition", "teamtypevPositionToVSCodePosition"],
    {vscode: {Position}},
)

const seeds = Number(process.env.POSITION_SEEDS ?? 40)
const cases = []
for (let seed = 1; seed <= seeds; seed++) {
    cases.push(...JSON.parse(execFileSync("python3", ["-I", path.join(__dirname, "position_reference.py"), String(seed), "200"], {maxBuffer: 1 << 28, encoding: "utf8"})))
}

const throws = f => { try { f(); return false } catch { return true } }

// 1. offset conversions (any string, lone surrogates included)
for (const c of cases) {
    assert.equal(c.s.length, c.units)
    for (let u = 0; u <= c.units + 3; u++) {
        const want = c.unit_to_char[String(u)]
        if (want === undefined) {
            assert.ok(throws(() => fns.UTF16CodeUnitOffsetToCharOffset(u, c.s)), `u2c must reject ${u} in ${JSON.stringify(c.s)}`)
        } else {
            assert.equal(fns.UTF16CodeUnitOffsetToCharOffset(u, c.s), want, `u2c ${u} in ${JSON.stringify(c.s)}`)
            assert.equal(fns.charOffsetToUTF16CodeUnitOffset(want, c.s), u, "inverse")
        }
    }
    for (let k = 0; k <= c.nchars + 3; k++) {
        if (k > c.nchars) assert.ok(throws(() => fns.charOffsetToUTF16CodeUnitOffset(k, c.s)))
        else assert.equal(fns.charOffsetToUTF16CodeUnitOffset(k, c.s), c.char_to_unit[k])
    }
    // [...s].length is the char count of the reference: valid scalar strings agree with Rust chars().count()
    assert.equal([...c.s].length, c.nchars)
}

// 2. VS Code line model (lines end at \r\n, \r, \n) vs daemon model (lines end at \n only, columns in chars).
const vscodeLines = text => text.split(/\r\n|\r|\n/)
const eols = text => text.match(/\r\n|\r|\n/g) ?? []
const lfLines = text => text.split("\n")
const hasLoneCR = text => /\r(?!\n)/.test(text)
const doc = text => ({lineCount: vscodeLines(text).length, lineAt: i => ({text: vscodeLines(text)[i]})})

function daemonPositionOfOffset(text, off) { // Rust Position::try_from_offset after the LF-only fix
    const chars = [...text].slice(0, off)
    const line = chars.filter(ch => ch === "\n").length
    const lastNl = chars.lastIndexOf("\n")
    return {line, character: chars.length - (lastNl + 1)}
}

let agreed = 0, disagreedLoneCR = 0
for (const c of cases) {
    const text = c.s
    if (/[\ud800-\udfff]/.test(text.replace(/[\ud800-\udbff][\udc00-\udfff]/g, ""))) continue // lone surrogates: see DESIGN.md
    const lines = vscodeLines(text), seps = eols(text)
    let base = 0 // char offset of line start
    for (let l = 0; l < lines.length; l++) {
        const lineChars = [...lines[l]].length
        for (let col = 0; col <= lineChars; col++) {
            const utf16 = fns.charOffsetToUTF16CodeUnitOffset(col, lines[l])
            const got = fns.vsCodePositionToTeamtypevPosition(lines, new Position(l, utf16))
            assert.deepEqual({...got}, {line: l, character: col})
            const want = daemonPositionOfOffset(text, base + col)
            if (hasLoneCR(text)) { if (want.line !== l) disagreedLoneCR++ ; continue }
            assert.deepEqual({...got}, want, `editor/daemon disagree at ${l}:${col} in ${JSON.stringify(text)}`)
            const back = fns.teamtypevPositionToVSCodePosition(doc(text), want)
            assert.deepEqual([back.line, back.character], [l, utf16])
            agreed++
        }
        base += lineChars + (seps[l] ? [...seps[l]].length : 0)
    }
}
// lone CR: VS Code starts a new line, the daemon does not -> unsafe to share (plugin refuses, see DESIGN.md)
assert.ok(disagreedLoneCR > 0)
// the Unicode breaks that ropey used to honour are plain characters for VS Code and the daemon
for (const brk of ["\u000b", "\u000c", "\u0085", " ", " "]) {
    assert.equal(vscodeLines(`a${brk}b\nc`).length, 2)
}
// daemon position between CR and LF of a CRLF has no VS Code position: the conversion throws, and the plugin must reject
assert.ok(throws(() => fns.teamtypevPositionToVSCodePosition(doc("a\r\nb"), {line: 0, character: 2})))
console.log(`position differential passed: ${cases.length} strings, ${agreed} editor/daemon position agreements, ${disagreedLoneCR} lone-CR disagreements (expected)`)
