#!/usr/bin/env python3
"""Mechanical correspondence check between Verus proof copies and repo source.

Proof files mark each copied item:
    // corr: <repo-relative-path> :: <selector>
    ...copy (with Verus specs / reviewed rewrites)...
    // corr-end
For every marker, this tool extracts the named item from the repo file, and
diffs it (normalized) against the proof copy. The diff must equal the stored
golden diff (golden/<id>.diff). Any drift on either side changes the diff.

usage: corr.py check|update [--repo DIR] [--proofs FILE...]
"""
import argparse, difflib, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
MARK = re.compile(r'^\s*//\s*corr:\s*(\S+)\s*::\s*(.+?)\s*$')
END = re.compile(r'^\s*//\s*corr-end\s*$')


def mask(src):
    """Same-length copy of src with comments and string/char contents blanked."""
    out = list(src); i = 0; n = len(src)
    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n': out[k] = ' '
    while i < n:
        c = src[i]
        if src.startswith('//', i):
            j = src.find('\n', i); j = n if j < 0 else j; blank(i, j); i = j
        elif src.startswith('/*', i):
            d = 1; j = i + 2
            while j < n and d:
                if src.startswith('/*', j): d += 1; j += 2
                elif src.startswith('*/', j): d -= 1; j += 2
                else: j += 1
            blank(i, j); i = j
        elif c == 'r' and re.match(r'r#*"', src[i:i+8]) and (i == 0 or not (src[i-1].isalnum() or src[i-1] == '_')):
            m = re.match(r'r(#*)"', src[i:]); h = m.group(1)
            e = src.find('"' + h, i + len(m.group(0)))
            e = n if e < 0 else e + 1 + len(h); blank(i + 1, e); i = e
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            blank(i + 1, j); i = j + 1
        elif c == "'":
            m = re.match(r"'(\\.[^']*|[^\\'])'", src[i:i+12])  # char literal, not lifetime
            if m: blank(i + 1, i + len(m.group(0)) - 1); i += len(m.group(0))
            else: i += 1
        else: i += 1
    return ''.join(out)


def match_brace(m, start):
    """index just past the } matching the first { at/after start (in masked m)."""
    i = m.index('{', start); d = 0
    while True:
        if m[i] == '{': d += 1
        elif m[i] == '}':
            d -= 1
            if d == 0: return i + 1
        i += 1


def line_start(s, i): return s.rfind('\n', 0, i) + 1


def with_attrs(src, a):
    """extend start a upward over contiguous #[..] attribute / doc-comment lines."""
    while True:
        p = line_start(src, a - 1) if a > 0 else 0
        prev = src[p:a].strip()
        if a > 0 and (prev.startswith('#[') or prev.startswith('///')): a = p
        else: return a


def find_item(src, sel):
    m = mask(src)
    kw = re.match(r'(struct|enum|type|trait|const|static|impl)\s+(.+)$', sel)
    if kw and '::' not in sel:
        k, name = kw.groups()
        pat = (r'^[ \t]*(pub(\([^)]*\))?\s+)?impl\b[^{;]*\b%s\b' if k == 'impl' else
               r'^[ \t]*(pub(\([^)]*\))?\s+)?%s\s+%s\b') % ((re.escape(name),) if k == 'impl' else (k, re.escape(name)))
        hits = [x for x in re.finditer(pat, m, re.M)]
        if len(hits) != 1: raise SystemExit(f'selector {sel!r}: {len(hits)} matches (need exactly 1)')
        s = hits[0].start()
        semi = m.find(';', s); br = m.find('{', s)
        e = semi + 1 if semi >= 0 and (br < 0 or semi < br) else match_brace(m, s)
        return src[with_attrs(src, s):e]
    # fn: "name" (top level or anywhere unique) or "Type::name"
    if '::' in sel:
        ty, name = sel.rsplit('::', 1)
        ranges = []
        for h in re.finditer(r'^[ \t]*(pub(\([^)]*\))?\s+)?impl\b[^{;]*\b%s\b[^{;]*\{' % re.escape(ty.split('::')[-1]), m, re.M):
            ranges.append((h.start(), match_brace(m, h.start())))
    else:
        name = sel; ranges = [(0, len(m))]
    pat = r'^[ \t]*(pub(\([^)]*\))?\s+)?(const\s+)?(async\s+)?(unsafe\s+)?fn\s+%s\b' % re.escape(name)
    hits = [(a + h.start()) for a, b in ranges for h in re.finditer(pat, m[a:b], re.M)]
    if len(hits) != 1: raise SystemExit(f'selector {sel!r}: {len(hits)} matches (need exactly 1)')
    s = hits[0]; semi = m.find(';', s); br = m.find('{', s)
    e = semi + 1 if semi >= 0 and (br < 0 or semi < br) else match_brace(m, s)
    return src[with_attrs(src, s):e]


def norm(text):
    lines = [l.rstrip() for l in text.expandtabs(4).split('\n')]
    lines = [l for l in lines if l.strip() and not l.strip().startswith('//')]
    ind = min((len(l) - len(l.lstrip()) for l in lines), default=0)
    return [l[ind:] for l in lines]


def regions(path):
    out = []; cur = None
    for no, line in enumerate(open(path, encoding='utf-8'), 1):
        mk = MARK.match(line)
        if mk:
            if cur: sys.exit(f'{path}:{no}: nested corr marker')
            cur = (mk.group(1), mk.group(2), no, []); continue
        if END.match(line):
            if not cur: sys.exit(f'{path}:{no}: corr-end without marker')
            out.append(cur); cur = None; continue
        if cur: cur[3].append(line.rstrip('\n'))
    if cur: sys.exit(f'{path}: unterminated corr marker at line {cur[2]}')
    return out


def golden_id(proof, rel, sel):
    tag = lambda s: re.sub(r'[^A-Za-z0-9]+', '_', s).strip('_')
    return f'{tag(os.path.relpath(proof, HERE + "/.."))}__{tag(rel)}__{tag(sel)}'


def make_diff(repo, proof, rel, sel, body):
    src = open(os.path.join(repo, rel), encoding='utf-8').read()
    a = norm(find_item(src, sel)); b = norm('\n'.join(body))
    d = [l for l in difflib.unified_diff(a, b, 'repo', 'proof', n=2, lineterm='') if not l.startswith('@@')]
    return '\n'.join(d) + ('\n' if d else '')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['check', 'update'])
    ap.add_argument('--repo', default=os.environ.get('TEAMTYPE_REPO', '/ssd1/sichangheagent/teamtype--teamtype'))
    ap.add_argument('--proofs', nargs='*', help='proof .rs files (default: listed in proofs.txt)')
    ap.add_argument('--golden', default=os.path.join(HERE, 'golden'))
    a = ap.parse_args()
    files = a.proofs or [os.path.normpath(os.path.join(HERE, l.strip())) for l in open(os.path.join(HERE, 'proofs.txt'))
                         if l.strip() and not l.startswith('#')]
    os.makedirs(a.golden, exist_ok=True)
    seen = set(); bad = 0; n = 0
    for f in files:
        for rel, sel, no, body in regions(f):
            gid = golden_id(f, rel, sel); gp = os.path.join(a.golden, gid + '.diff'); seen.add(gid + '.diff'); n += 1
            if gid in {g[:-5] for g in seen if g != gid + '.diff'}: sys.exit('duplicate marker ' + gid)
            d = make_diff(a.repo, f, rel, sel, body)
            if a.mode == 'update':
                open(gp, 'w').write(d); print('wrote', gid, f'({d.count(chr(10))} diff lines)'); continue
            if not os.path.exists(gp): print(f'FAIL {f}:{no} {rel} :: {sel}: no golden (run update, review)'); bad += 1; continue
            g = open(gp).read()
            if g != d:
                bad += 1; print(f'FAIL {f}:{no} {rel} :: {sel}: diff differs from reviewed golden')
                sys.stdout.writelines(difflib.unified_diff(g.splitlines(1), d.splitlines(1), 'golden', 'now'))
    if a.mode == 'check':
        if not a.proofs:
            for g in sorted(os.listdir(a.golden)):
                if g.endswith('.diff') and g not in seen: print('FAIL orphan golden', g); bad += 1
        print(f'corr: {n} regions, {bad} failures'); sys.exit(1 if bad else 0)


main()
