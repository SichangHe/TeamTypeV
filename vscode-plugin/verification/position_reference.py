# SPDX-License-Identifier: AGPL-3.0-or-later
"""Independent reference for UTF-16 <-> char offsets, written from the definition (not from
extension.ts). A JS string is a sequence of UTF-16 code units; a "char" is a surrogate pair
(high then low) or any other single code unit (a lone surrogate is one char of width 1,
exactly what JS spread iteration yields). Emits JSON cases on stdout."""
import json, random, sys

ATOMS = ["a", "b", " ", "é", "é", "字", "🥕", "😀", "\r", "\n", "\r\n", "\u000b", "\u000c",
         "\u0085", " ", " ", "\ud800", "\udc00", "\udbff", "\udfff", "‍", "𝒜"]

def units(s):
    out = []
    for ch in s:
        c = ord(ch)
        if c >= 0x10000:
            c -= 0x10000
            out += [0xD800 + (c >> 10), 0xDC00 + (c & 0x3FF)]
        else:
            out.append(c)
    return out

def chars(s):
    """list of widths of each char of the JS string s (python str that may hold surrogates)."""
    u, i, w = units(s), 0, []
    while i < len(u):
        if 0xD800 <= u[i] <= 0xDBFF and i + 1 < len(u) and 0xDC00 <= u[i + 1] <= 0xDFFF:
            w.append(2); i += 2
        else:
            w.append(1); i += 1
    return w

def js_string(parts):
    # build a python str whose code units are exactly the JS string's; a high surrogate
    # followed by a low one must stay two units, which python would store as two code points
    return "".join(parts)

def expected(s):
    w = chars(s)
    n_units = sum(w)
    char_to_unit = [sum(w[:k]) for k in range(len(w) + 1)]
    unit_to_char = {u: k for k, u in enumerate(char_to_unit)}
    return n_units, char_to_unit, unit_to_char

def cases(seed, n):
    rng = random.Random(seed)
    out = []
    for _ in range(n):
        s = "".join(rng.choice(ATOMS) for _ in range(rng.randint(0, 8)))
        # python keeps "\ud83d" "\ude00" as two code points, so a lone-surrogate pair adjacent
        # to each other is a real pair in UTF-16 terms: units() above handles only >=0x10000
        # code points; normalise by re-encoding through utf-16 with surrogatepass.
        s = s.encode("utf-16-le", "surrogatepass").decode("utf-16-le", "surrogatepass")
        n_units, c2u, u2c = expected(s)
        out.append({
            "s": s, "units": n_units, "nchars": len(c2u) - 1,
            "char_to_unit": c2u,
            "unit_to_char": {str(u): k for u, k in u2c.items()},
        })
    return out

if __name__ == "__main__":
    json.dump(cases(int(sys.argv[1]), int(sys.argv[2])), sys.stdout)
