// Verus model of TeamType's file-URI conversion (crates/teamtype/src/path.rs, origin/main):
//   AbsolutePath::to_file_uri  = Url::from_file_path(p).to_string()
//   FileUri::to_absolute_path  = Url::parse(s).to_file_path()
// against the vendored `url` 2.5.8 / `percent-encoding` 2.3.2 Unix code. See DESIGN.md.
use vstd::prelude::*;

verus! {

pub type B = Seq<u8>;

// ---------- encode set (url-2.5.8/src/parser.rs:20-42, lib.rs:2948 `SPECIAL_PATH_SEGMENT`) ----------
// CONTROLS = <0x20, >0x7e (percent-encoding AsciiSet; non-ASCII always encoded);
// FRAGMENT adds ' ' '"' '<' '>' '`'; PATH adds '#' '?' '{' '}'; PATH_SEGMENT adds '/' '%';
// SPECIAL_PATH_SEGMENT adds '\\'.  (This is the encoder's set; negative controls edit it.)
pub open spec fn in_enc_set(b: u8) -> bool {
    b < 0x20 || b > 0x7e
    || b == 0x20 || b == 0x22 || b == 0x3c || b == 0x3e || b == 0x60 // ' ' " < > `
    || b == 0x23 || b == 0x3f || b == 0x7b || b == 0x7d              // # ? { }
    || b == 0x2f || b == 0x25                                        // / %
    || b == 0x5c                                                     // backslash
}

// The parser's PATH set (parser.rs:23): what `parse_path` re-encodes in-place.
pub open spec fn in_path_set(b: u8) -> bool {
    b < 0x20 || b > 0x7e
    || b == 0x20 || b == 0x22 || b == 0x3c || b == 0x3e || b == 0x60
    || b == 0x23 || b == 0x3f || b == 0x7b || b == 0x7d
}

pub open spec fn hexd(n: int) -> u8 { if n < 10 { (48 + n) as u8 } else { (55 + n) as u8 } } // uppercase
pub open spec fn hv(d: u8) -> int {
    if 48 <= d <= 57 { d - 48 } else if 65 <= d <= 70 { d - 55 } else if 97 <= d <= 102 { d - 87 } else { -1 }
}

pub open spec fn enc_byte(b: u8) -> B {
    if in_enc_set(b) { seq![37u8, hexd((b / 16) as int), hexd((b % 16) as int)] } else { seq![b] }
}
// percent_encode(bytes, SPECIAL_PATH_SEGMENT) (per-byte, per component)
pub open spec fn enc(s: B) -> B decreases s.len() {
    if s.len() == 0 { Seq::empty() } else { enc_byte(s[0]) + enc(s.skip(1)) }
}
// percent_decode(bytes) (percent-encoding lib.rs: '%' + two hex digits -> byte, else literal)
pub open spec fn dec(b: B) -> B decreases b.len() {
    if b.len() == 0 { Seq::empty() }
    else if b[0] == 37 && b.len() >= 3 && hv(b[1]) >= 0 && hv(b[2]) >= 0 {
        seq![(hv(b[1]) * 16 + hv(b[2])) as u8] + dec(b.skip(3))
    } else { seq![b[0]] + dec(b.skip(1)) }
}

// ---------- splitting / joining on '/' ----------
pub open spec fn pieces_acc(b: B, cur: B) -> Seq<B> decreases b.len() {
    if b.len() == 0 { seq![cur] }
    else if b[0] == 47 { seq![cur] + pieces_acc(b.skip(1), Seq::empty()) }
    else { pieces_acc(b.skip(1), cur.push(b[0])) }
}
pub open spec fn pieces(b: B) -> Seq<B> { pieces_acc(b, Seq::empty()) } // str::split('/')

pub open spec fn tj(segs: Seq<B>) -> B decreases segs.len() { // "/s0/s1/..."
    if segs.len() == 0 { Seq::empty() } else { seq![47u8] + segs[0] + tj(segs.skip(1)) }
}

pub open spec fn dot() -> B { seq![46u8] }
pub open spec fn dotdot() -> B { seq![46u8, 46u8] }

// std `Path::components` on an absolute Unix path, as a list of component byte strings:
// split on '/', drop empty pieces (repeated/trailing slashes) and "." (CurDir). Keeps "..".
pub open spec fn filt(ps: Seq<B>) -> Seq<B> decreases ps.len() {
    if ps.len() == 0 { Seq::empty() }
    else { (if ps[0].len() > 0 && ps[0] != dot() { seq![ps[0]] } else { Seq::empty() }) + filt(ps.skip(1)) }
}
pub open spec fn comps_of(p: B) -> Seq<B> { filt(pieces(p)) }

pub open spec fn no_slash(s: B) -> bool { forall|i: int| 0 <= i < s.len() ==> s[i] != 47 }
pub open spec fn valid_comps(c: Seq<B>) -> bool {
    forall|k: int| 0 <= k < c.len() ==> c[k].len() > 0 && no_slash(c[k]) && c[k] != dot()
}
pub open spec fn no_dd(c: Seq<B>) -> bool { forall|k: int| 0 <= k < c.len() ==> c[k] != dotdot() }

// ---------- to_file_uri: path part of the serialization (lib.rs:2948-2985) ----------
// "file://" ++ for each component after root: '/' ++ percent_encode(component); empty -> "/"
pub open spec fn ser(c: Seq<B>) -> B {
    if c.len() == 0 { seq![47u8] } else { tj(c.map_values(|s: B| enc(s))) }
}

// ---------- Url::parse of that string, path part (parser.rs:512-560 file/file-host, 1189-1395 parse_path) ----------
// MODEL: for input "/p0/p1/.." that is "clean" the parser returns the same pieces; any piece that is
// a (percent-encoded) dot segment, an empty inner piece, or contains a byte the path state would
// rewrite/terminate on ('#','?', controls, ' ', '\\' ...) is OUTSIDE the modelled domain => None.
pub open spec fn clean_byte(b: u8) -> bool { !in_path_set(b) && b != 0x5c && b != 47 }
pub open spec fn clean(s: B) -> bool { forall|i: int| 0 <= i < s.len() ==> clean_byte(s[i]) }
pub open spec fn dot_pattern(p: B) -> bool { dec(p) == dot() || dec(p) == dotdot() } // ".", "%2e", "..", "%2e%2E", ".%2e" ...
pub open spec fn parse_ok(ps: Seq<B>) -> bool {
    forall|k: int| 0 <= k < ps.len() ==>
        clean(ps[k]) && !dot_pattern(ps[k]) && (ps[k].len() > 0 || ps.len() == 1)
}
pub open spec fn uparse(p: B) -> Option<Seq<B>> { // Url::path_segments() of the parsed URL
    if p.len() >= 1 && p[0] == 47 {
        let ps = pieces(p.skip(1));
        if parse_ok(ps) { Some(ps) } else { None }
    } else { None }
}

// ---------- Url::to_file_path (lib.rs:3064-3115, Unix) ----------
pub open spec fn is_alpha(b: u8) -> bool { (65 <= b <= 90) || (97 <= b <= 122) }
pub open spec fn decsegs(ps: Seq<B>) -> Seq<B> { ps.map_values(|s: B| dec(s)) }
pub open spec fn to_file_path_bytes(ps: Seq<B>) -> B {
    let bytes = tj(decsegs(ps));
    // "A windows drive letter must end with a slash." (applies on Unix too)
    if bytes.len() > 2 && is_alpha(bytes[bytes.len() - 2])
        && (bytes[bytes.len() - 1] == 58 || bytes[bytes.len() - 1] == 124) { bytes + seq![47u8] } else { bytes }
}

// ---------- lemmas ----------
proof fn hv_hexd(n: int) requires 0 <= n < 16 ensures hv(hexd(n)) == n {}

proof fn dec_enc_byte(b: u8, r: B) ensures dec(enc_byte(b) + r) == seq![b] + dec(r) {
    let s = enc_byte(b) + r;
    if in_enc_set(b) {
        hv_hexd((b / 16) as int); hv_hexd((b % 16) as int);
        assert(s[0] == 37u8); assert(s[1] == hexd((b / 16) as int)); assert(s[2] == hexd((b % 16) as int));
        assert(s.skip(3) =~= r);
        assert(((b / 16) as int * 16 + (b % 16) as int) as u8 == b);
    } else {
        assert(s[0] == b); assert(b != 37);
        assert(s.skip(1) =~= r);
    }
}

proof fn enc_dec(s: B) ensures dec(enc(s)) == s decreases s.len() {
    if s.len() > 0 {
        enc_dec(s.skip(1));
        dec_enc_byte(s[0], enc(s.skip(1)));
        assert(seq![s[0]] + s.skip(1) =~= s);
    }
}

proof fn enc_byte_clean(b: u8) ensures clean(enc_byte(b)) {
    if in_enc_set(b) {
        let s = enc_byte(b);
        assert forall|i: int| 0 <= i < s.len() implies clean_byte(s[i]) by {
            let h1 = hexd((b / 16) as int); let h2 = hexd((b % 16) as int);
            assert(h1 == 48 + (b / 16) || h1 == 55 + (b / 16));
            assert(h2 == 48 + (b % 16) || h2 == 55 + (b % 16));
            if i == 0 { assert(s[0] == 37u8); } else if i == 1 { assert(s[1] == h1); } else { assert(s[2] == h2); }
        }
    }
}

proof fn clean_add(a: B, b: B) requires clean(a), clean(b) ensures clean(a + b) {
    assert forall|i: int| 0 <= i < (a + b).len() implies clean_byte((a + b)[i]) by {
        if i < a.len() { assert((a + b)[i] == a[i]); } else { assert((a + b)[i] == b[i - a.len()]); }
    }
}

proof fn enc_clean(s: B) ensures clean(enc(s)) decreases s.len() {
    if s.len() > 0 { enc_byte_clean(s[0]); enc_clean(s.skip(1)); clean_add(enc_byte(s[0]), enc(s.skip(1))); }
}

proof fn enc_nonempty(s: B) requires s.len() > 0 ensures enc(s).len() > 0 {
    let e = enc_byte(s[0]);
    assert(e.len() >= 1);
    assert(enc(s) == e + enc(s.skip(1)));
}

proof fn cancel_head(h: B, a: Seq<B>, b: Seq<B>) requires seq![h] + a == seq![h] + b ensures a == b {
    assert((seq![h] + a).len() == 1 + a.len());
    assert((seq![h] + b).len() == 1 + b.len());
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        assert((seq![h] + a)[i + 1] == a[i]); assert((seq![h] + b)[i + 1] == b[i]);
    }
    assert(a =~= b);
}

proof fn pieces_nonempty(b: B, cur: B) ensures pieces_acc(b, cur).len() > 0 decreases b.len() {
    if b.len() > 0 && b[0] != 47 { pieces_nonempty(b.skip(1), cur.push(b[0])); }
}

proof fn tj_single(e: B) ensures tj(seq![e]) == seq![47u8] + e {
    let d = seq![e];
    assert(d.skip(1).len() == 0);
    assert(tj(d.skip(1)) =~= Seq::<u8>::empty());
    assert(tj(d) == seq![47u8] + d[0] + tj(d.skip(1)));
    assert(seq![47u8] + e + Seq::<u8>::empty() =~= seq![47u8] + e);
}

proof fn filt_head_empty(d: Seq<B>) ensures filt(seq![Seq::<u8>::empty()] + d) == filt(d) {
    let l = seq![Seq::<u8>::empty()] + d;
    assert(l.skip(1) =~= d);
    assert(l[0] =~= Seq::<u8>::empty());
    assert(l.len() > 0);
    assert(filt(l) == (if l[0].len() > 0 && l[0] != dot() { seq![l[0]] } else { Seq::empty() }) + filt(l.skip(1)));
    assert(Seq::<B>::empty() + filt(d) =~= filt(d));
}

proof fn pieces_acc_noslash(a: B, cur: B)
    requires no_slash(a)
    ensures pieces_acc(a, cur) == seq![cur + a]
    decreases a.len()
{
    if a.len() > 0 {
        assert(a[0] != 47);
        assert(no_slash(a.skip(1))) by { assert forall|i: int| 0 <= i < a.skip(1).len() implies a.skip(1)[i] != 47 by { assert(a.skip(1)[i] == a[i + 1]); } }
        pieces_acc_noslash(a.skip(1), cur.push(a[0]));
        assert(cur.push(a[0]) + a.skip(1) =~= cur + a);
    } else { assert(cur + a =~= cur); }
}

// pieces_acc(a ++ "/" ++ r, cur) == [cur ++ a] ++ pieces(r)
proof fn pieces_acc_split(a: B, r: B, cur: B)
    requires no_slash(a)
    ensures pieces_acc(a + seq![47u8] + r, cur) == seq![cur + a] + pieces(r)
    decreases a.len()
{
    let x = a + seq![47u8] + r;
    if a.len() == 0 {
        assert(x[0] == 47u8);
        assert(x.skip(1) =~= r);
        assert(cur + a =~= cur);
    } else {
        assert(x[0] == a[0]); assert(a[0] != 47);
        assert(x.skip(1) =~= a.skip(1) + seq![47u8] + r);
        assert(no_slash(a.skip(1))) by { assert forall|i: int| 0 <= i < a.skip(1).len() implies a.skip(1)[i] != 47 by { assert(a.skip(1)[i] == a[i + 1]); } }
        pieces_acc_split(a.skip(1), r, cur.push(a[0]));
        assert(cur.push(a[0]) + a.skip(1) =~= cur + a);
    }
}

pub open spec fn all_noslash(c: Seq<B>) -> bool { forall|k: int| 0 <= k < c.len() ==> no_slash(c[k]) }

// pieces("/s0/s1/../sn") == [""] ++ segs   (segs nonempty list, no '/' inside)
proof fn pieces_tj(c: Seq<B>)
    requires all_noslash(c), c.len() > 0
    ensures pieces(tj(c)) == seq![Seq::<u8>::empty()] + c
    decreases c.len()
{
    let t = tj(c);
    let x = c[0] + tj(c.skip(1));
    assert(t == seq![47u8] + x);
    assert(t[0] == 47u8);
    assert(t.skip(1) =~= x);
    // pieces(t) = [empty] ++ pieces_acc(x, empty)
    assert(pieces(t) == seq![Seq::<u8>::empty()] + pieces_acc(x, Seq::empty()));
    if c.len() == 1 {
        assert(tj(c.skip(1)) =~= Seq::<u8>::empty());
        assert(x =~= c[0]);
        pieces_acc_noslash(c[0], Seq::empty());
        assert(Seq::<u8>::empty() + c[0] =~= c[0]);
        assert(seq![c[0]] =~= c);
    } else {
        let rest = c.skip(1);
        assert(all_noslash(rest)) by { assert forall|k: int| 0 <= k < rest.len() implies no_slash(rest[k]) by { assert(rest[k] == c[k + 1]); } }
        pieces_tj(rest);
        let tr = tj(rest);
        let y = tr.skip(1);
        assert(tr[0] == 47u8);
        assert(x =~= c[0] + seq![47u8] + y) by { assert(tr =~= seq![47u8] + y); }
        pieces_acc_split(c[0], y, Seq::empty());
        assert(Seq::<u8>::empty() + c[0] =~= c[0]);
        // pieces(tr) == [empty] ++ pieces(y)
        assert(pieces(tr) == seq![Seq::<u8>::empty()] + pieces(y));
        cancel_head(Seq::empty(), pieces(y), rest);
        assert(seq![c[0]] + rest =~= c);
    }
}

proof fn tj_snoc_empty(c: Seq<B>)
    ensures tj(c.push(Seq::empty())) == tj(c) + seq![47u8]
    decreases c.len()
{
    let d = c.push(Seq::empty());
    if c.len() == 0 {
        assert(d.skip(1) =~= Seq::<B>::empty());
        assert(d =~= seq![Seq::<u8>::empty()]);
        tj_single(Seq::empty());
        assert(seq![47u8] + Seq::<u8>::empty() =~= seq![47u8]);
        assert(tj(c) =~= Seq::<u8>::empty());
    } else {
        assert(d[0] == c[0]);
        assert(d.skip(1) =~= c.skip(1).push(Seq::empty()));
        tj_snoc_empty(c.skip(1));
        assert(tj(d) =~= seq![47u8] + c[0] + (tj(c.skip(1)) + seq![47u8]));
        assert(tj(c) =~= seq![47u8] + c[0] + tj(c.skip(1)));
    }
}

proof fn filt_valid(c: Seq<B>) requires valid_comps(c) ensures filt(c) == c decreases c.len() {
    if c.len() > 0 {
        let r = c.skip(1);
        assert(valid_comps(r)) by { assert forall|k: int| 0 <= k < r.len() implies r[k].len() > 0 && no_slash(r[k]) && r[k] != dot() by { assert(r[k] == c[k + 1]); } }
        filt_valid(r);
        assert(seq![c[0]] + r =~= c);
    }
}

proof fn filt_trail(c: Seq<B>) requires valid_comps(c) ensures filt(c.push(Seq::empty())) == c decreases c.len() {
    let d = c.push(Seq::empty());
    if c.len() == 0 {
        assert(d =~= seq![Seq::<u8>::empty()]);
        filt_head_empty(Seq::empty());
    } else {
        let r = c.skip(1);
        assert(valid_comps(r)) by { assert forall|k: int| 0 <= k < r.len() implies r[k].len() > 0 && no_slash(r[k]) && r[k] != dot() by { assert(r[k] == c[k + 1]); } }
        assert(d.skip(1) =~= r.push(Seq::empty()));
        filt_trail(r);
        assert(d[0] == c[0]);
        assert(c[0].len() > 0 && c[0] != dot());
        assert(filt(d) == seq![c[0]] + filt(d.skip(1)));
        assert(seq![c[0]] + r =~= c);
    }
}

// pieces yield slash-free pieces; so comps_of yields valid components
proof fn pieces_acc_valid(b: B, cur: B)
    requires no_slash(cur)
    ensures forall|k: int| 0 <= k < pieces_acc(b, cur).len() ==> no_slash(pieces_acc(b, cur)[k])
    decreases b.len()
{
    if b.len() == 0 {
        assert(pieces_acc(b, cur) == seq![cur]);
    } else {
        if b[0] == 47 {
            assert(no_slash(Seq::<u8>::empty()));
            pieces_acc_valid(b.skip(1), Seq::empty());
            assert(pieces_acc(b, cur) == seq![cur] + pieces_acc(b.skip(1), Seq::empty()));
            let r = pieces_acc(b.skip(1), Seq::empty());
            let all = seq![cur] + r;
            assert forall|k: int| 0 <= k < all.len() implies no_slash(all[k]) by {
                if k > 0 { assert(all[k] == r[k - 1]); }
            }
        } else {
            let c2 = cur.push(b[0]);
            assert(no_slash(c2)) by { assert forall|i: int| 0 <= i < c2.len() implies c2[i] != 47 by { if i < cur.len() { assert(c2[i] == cur[i]); } } }
            pieces_acc_valid(b.skip(1), c2);
            assert(pieces_acc(b, cur) == pieces_acc(b.skip(1), c2));
        }
    }
}
proof fn filt_valid_out(ps: Seq<B>)
    requires forall|k: int| 0 <= k < ps.len() ==> no_slash(ps[k])
    ensures valid_comps(filt(ps))
    decreases ps.len()
{
    if ps.len() > 0 {
        let r = ps.skip(1);
        assert(forall|k: int| 0 <= k < r.len() ==> no_slash(r[k])) by { assert forall|k: int| 0 <= k < r.len() implies no_slash(r[k]) by { assert(r[k] == ps[k + 1]); } }
        filt_valid_out(r);
        let h: Seq<B> = if ps[0].len() > 0 && ps[0] != dot() { seq![ps[0]] } else { Seq::empty() };
        let f = h + filt(r);
        assert forall|k: int| 0 <= k < f.len() implies f[k].len() > 0 && no_slash(f[k]) && f[k] != dot() by {
            if k < h.len() { assert(f[k] == h[k]); } else { assert(f[k] == filt(r)[k - h.len()]); }
        }
    }
}
proof fn comps_valid(p: B) ensures valid_comps(comps_of(p)) {
    pieces_acc_valid(p, Seq::empty());
    filt_valid_out(pieces(p));
}

// ---------- main theorem (on component lists) ----------
// For valid components c (what std yields) without "..": the URL parses within the modelled domain and
// to_file_path returns bytes whose components are again c.
proof fn roundtrip_comps(c: Seq<B>)
    requires valid_comps(c), no_dd(c)
    ensures
        uparse(ser(c)).is_some(),
        comps_of(to_file_path_bytes(uparse(ser(c)).unwrap())) == c,
{
    let p = ser(c);
    if c.len() == 0 {
        assert(p =~= seq![47u8]);
        assert(p.skip(1) =~= Seq::<u8>::empty());
        let ps = pieces(p.skip(1));
        assert(ps =~= seq![Seq::<u8>::empty()]);
        assert(parse_ok(ps)) by {
            assert(dec(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
        }
        assert(decsegs(ps) =~= seq![Seq::<u8>::empty()]);
        let bytes = tj(decsegs(ps));
        tj_single(Seq::empty());
        assert(seq![47u8] + Seq::<u8>::empty() =~= seq![47u8]);
        assert(bytes =~= seq![47u8]);
        assert(!(bytes.len() > 2));
        let e0 = Seq::<u8>::empty();
        assert(all_noslash(seq![e0])) by { assert(no_slash(e0)); }
        pieces_tj(seq![e0]);
        filt_head_empty(seq![e0]);
        filt_trail(Seq::empty());
        assert(seq![e0] =~= Seq::<B>::empty().push(e0));
    } else {
        let m = c.map_values(|s: B| enc(s));
        assert forall|k: int| 0 <= k < m.len() implies no_slash(m[k]) && clean(m[k]) && m[k].len() > 0 by {
            enc_clean(c[k]); enc_nonempty(c[k]);
            assert(m[k] == enc(c[k]));
            let e = m[k];
            assert forall|i: int| 0 <= i < e.len() implies e[i] != 47 by { assert(clean_byte(e[i])); }
        }
        pieces_tj(m);
        let t = tj(m);
        assert(t == p);
        assert(t[0] == 47u8);
        assert(t =~= seq![47u8] + t.skip(1));
        assert(pieces(t) == seq![Seq::<u8>::empty()] + pieces(t.skip(1)));
        let ps = pieces(p.skip(1));
        cancel_head(Seq::empty(), ps, m);
        assert forall|k: int| 0 <= k < ps.len() implies clean(ps[k]) && !dot_pattern(ps[k]) && (ps[k].len() > 0 || ps.len() == 1) by {
            enc_dec(c[k]);
            assert(ps[k] == enc(c[k]));
            assert(dec(ps[k]) == c[k]);
        }
        assert(parse_ok(ps));
        // decoding gives back the components
        assert(decsegs(ps) =~= c) by {
            assert forall|k: int| 0 <= k < c.len() implies decsegs(ps)[k] == c[k] by { enc_dec(c[k]); }
        }
        let bytes = tj(c);
        pieces_tj(c);
        if bytes.len() > 2 && is_alpha(bytes[bytes.len() - 2])
            && (bytes[bytes.len() - 1] == 58 || bytes[bytes.len() - 1] == 124) {
            // appended trailing '/'
            tj_snoc_empty(c);
            let d = c.push(Seq::empty());
            assert(all_noslash(d)) by { assert forall|k: int| 0 <= k < d.len() implies no_slash(d[k]) by { if k < c.len() { assert(d[k] == c[k]); } else { assert(d[k] =~= Seq::<u8>::empty()); } } }
            pieces_tj(d);
            assert(seq![Seq::<u8>::empty()] + d =~= seq![Seq::<u8>::empty()] + c.push(Seq::empty()));
            assert(pieces(tj(d)) == seq![Seq::<u8>::empty()] + d);
            assert(tj(d) == bytes + seq![47u8]);
            // filt([empty] ++ c ++ [empty]) == c
            let e0 = Seq::<u8>::empty();
            filt_head_empty(d);
            filt_trail(c);
        } else {
            let e0 = Seq::<u8>::empty();
            filt_head_empty(c);
            filt_valid(c);
        }
    }
}

// ---------- full statement on bytes ----------
// to_file_uri path-part for an absolute path p = ser(components(p)); round trip preserves Path equality
// (std PathBuf equality compares components).
pub open spec fn to_uri_path(p: B) -> B { ser(comps_of(p)) }
pub open spec fn back(uri_path: B) -> B { to_file_path_bytes(uparse(uri_path).unwrap()) }

proof fn thm_roundtrip(p: B)
    requires p.len() > 0, p[0] == 47, no_dd(comps_of(p))
    ensures
        uparse(to_uri_path(p)).is_some(),
        comps_of(back(to_uri_path(p))) == comps_of(p),
        back(to_uri_path(p)).len() > 0 && back(to_uri_path(p))[0] == 47, // result is absolute
{
    comps_valid(p);
    roundtrip_comps(comps_of(p));
    let c = comps_of(p);
    let q = to_uri_path(p);
    let bytes = back(q);
    let ps = uparse(q).unwrap();
    assert(q[0] == 47u8) by { if c.len() == 0 { assert(q =~= seq![47u8]); } else { let m = c.map_values(|s: B| enc(s)); assert(q == tj(m)); } }
    pieces_nonempty(q.skip(1), Seq::empty());
    assert(decsegs(ps).len() > 0);
    assert(tj(decsegs(ps))[0] == 47u8);
}

// ---------- injectivity: different paths never share a URI ----------
proof fn thm_injective(p1: B, p2: B)
    requires p1.len() > 0, p1[0] == 47, p2.len() > 0, p2[0] == 47,
        to_uri_path(p1) == to_uri_path(p2)
    ensures comps_of(p1) == comps_of(p2)
{
    comps_valid(p1); comps_valid(p2);
    let c1 = comps_of(p1); let c2 = comps_of(p2);
    let u = ser(c1);
    if c1.len() == 0 || c2.len() == 0 {
        if c1.len() == 0 && c2.len() > 0 {
            let m2 = c2.map_values(|s: B| enc(s));
            assert(c2[0].len() > 0); enc_nonempty(c2[0]);
            assert(m2[0] == enc(c2[0]));
            assert(tj(m2) == seq![47u8] + m2[0] + tj(m2.skip(1)));
            assert(tj(m2).len() >= 2);
        } else if c2.len() == 0 && c1.len() > 0 {
            let m1 = c1.map_values(|s: B| enc(s));
            assert(c1[0].len() > 0); enc_nonempty(c1[0]);
            assert(m1[0] == enc(c1[0]));
            assert(tj(m1) == seq![47u8] + m1[0] + tj(m1.skip(1)));
            assert(tj(m1).len() >= 2);
        }
    } else {
        let m1 = c1.map_values(|s: B| enc(s)); let m2 = c2.map_values(|s: B| enc(s));
        assert forall|k: int| 0 <= k < m1.len() implies no_slash(m1[k]) by {
            enc_clean(c1[k]); let e = m1[k]; assert(e == enc(c1[k]));
            assert forall|i: int| 0 <= i < e.len() implies e[i] != 47 by { assert(clean_byte(e[i])); }
        }
        assert forall|k: int| 0 <= k < m2.len() implies no_slash(m2[k]) by {
            enc_clean(c2[k]); let e = m2[k]; assert(e == enc(c2[k]));
            assert forall|i: int| 0 <= i < e.len() implies e[i] != 47 by { assert(clean_byte(e[i])); }
        }
        pieces_tj(m1); pieces_tj(m2);
        assert(seq![Seq::<u8>::empty()] + m1 =~= seq![Seq::<u8>::empty()] + m2);
        cancel_head(Seq::empty(), m1, m2);
        assert(c1.len() == c2.len());
        assert forall|k: int| 0 <= k < c1.len() implies c1[k] == c2[k] by {
            enc_dec(c1[k]); enc_dec(c2[k]);
            assert(m1[k] == enc(c1[k])); assert(m2[k] == enc(c2[k]));
        }
        assert(c1 =~= c2);
    }
}

} // verus!
fn main() {}
