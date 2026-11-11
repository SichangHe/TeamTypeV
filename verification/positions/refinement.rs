// Verus refinement of teamtype `Position::{try_from_offset, try_to_offset}`
// (source/types.rs). Exec bodies below are the source bodies with only the
// rewrites listed in REFINEMENT.md ("rewrites"). Ropey is trusted via the
// external_body specs + `axiom_rope_wf`, which src/bin/ropey_axioms.rs tests
// against the real Ropey 1.6.1.
use vstd::prelude::*;

verus! {

// ---------- trusted Ropey model (ASSUMED) ----------
// s = content as Unicode scalar sequence; lines as Ropey splits them.
pub uninterp spec fn nlines(s: Seq<char>) -> int;
pub uninterp spec fn start(s: Seq<char>, l: int) -> int;      // line_to_char
pub uninterp spec fn ends_lf(s: Seq<char>, l: int) -> bool;   // line l's last char == '\n'
pub uninterp spec fn line_of(s: Seq<char>, o: int) -> int;    // char_to_line

pub open spec fn n(s: Seq<char>) -> int { s.len() as int }
pub open spec fn last(s: Seq<char>) -> int { nlines(s) - 1 }
pub open spec fn line_len(s: Seq<char>, l: int) -> int {
    if l < last(s) { start(s, l + 1) - start(s, l) } else { n(s) - start(s, l) }
}

pub open spec fn rope_wf(s: Seq<char>) -> bool {
    &&& 1 <= nlines(s) <= n(s) + 1
    &&& n(s) <= usize::MAX
    &&& start(s, 0) == 0
    &&& start(s, last(s)) <= n(s)
    // every non-last line ends with a non-empty terminator
    &&& forall|i: int, j: int| 0 <= i < j < nlines(s) ==> #[trigger] start(s, i) < #[trigger] start(s, j)
    // the last line has no terminator, so it never ends in LF
    &&& !ends_lf(s, last(s))
    &&& forall|o: int| 0 <= o <= n(s) ==> {
        let l = #[trigger] line_of(s, o);
        &&& 0 <= l < nlines(s)
        &&& start(s, l) <= o
        &&& (l == last(s) || o < start(s, l + 1))
    }
}

#[verifier::external_body]
pub proof fn axiom_rope_wf(s: Seq<char>)
    ensures rope_wf(s),
{}

pub struct Error;

#[verifier::external_body]
pub struct Rope { inner: () }
#[verifier::external_body]
pub struct RopeSlice { inner: () }

impl Rope {
    pub uninterp spec fn view(&self) -> Seq<char>;

    #[verifier::external_body]
    pub fn from_str(content: &str) -> (r: Rope)
        ensures r@ == content@,
    { unimplemented!() }

    #[verifier::external_body]
    pub fn len_lines(&self) -> (r: usize)
        ensures r == nlines(self@),
    { unimplemented!() }

    #[verifier::external_body]
    pub fn try_char_to_line(&self, o: usize) -> (r: Result<usize, Error>)
        ensures
            o <= n(self@) ==> r == Ok::<usize, Error>(line_of(self@, o as int) as usize),
            o > n(self@) ==> r is Err,
    { unimplemented!() }

    // Ropey accepts one-past-the-end line index, returning len_chars.
    #[verifier::external_body]
    pub fn try_line_to_char(&self, l: usize) -> (r: Result<usize, Error>)
        ensures
            l < nlines(self@) ==> r == Ok::<usize, Error>(start(self@, l as int) as usize),
            l == nlines(self@) ==> r == Ok::<usize, Error>(n(self@) as usize),
            l > nlines(self@) ==> r is Err,
    { unimplemented!() }

    #[verifier::external_body]
    pub fn line(&self, l: usize) -> (r: RopeSlice)
        requires l < nlines(self@),
        ensures r.len() == line_len(self@, l as int), r.last_lf() == ends_lf(self@, l as int),
    { unimplemented!() }
}

impl RopeSlice {
    pub uninterp spec fn len(&self) -> int;
    pub uninterp spec fn last_lf(&self) -> bool;

    #[verifier::external_body]
    pub fn len_chars(&self) -> (r: usize) ensures r == self.len(),
    { unimplemented!() }

    // stands for `self.chars().last() == Some('\n')`
    #[verifier::external_body]
    pub fn chars_last_is_lf(&self) -> (r: bool) ensures r == self.last_lf(),
    { unimplemented!() }
}

// ---------- functional specs ----------
pub struct Position { pub line: usize, pub character: usize }

pub open spec fn bound(s: Seq<char>, l: int) -> int {
    line_len(s, l) - if ends_lf(s, l) { 1int } else { 0int }
}
pub open spec fn g_ok(s: Seq<char>, l: int, c: int) -> bool { 0 <= l < nlines(s) && 0 <= c <= bound(s, l) }

// fixed variant: strip the terminator of every non-last line
pub open spec fn bound_fixed(s: Seq<char>, l: int) -> int {
    line_len(s, l) - if l < last(s) { 1int } else { 0int }
}
pub open spec fn g_fixed_ok(s: Seq<char>, l: int, c: int) -> bool { 0 <= l < nlines(s) && 0 <= c <= bound_fixed(s, l) }

// ---------- the real code ----------
impl Position {
    // corr: crates/teamtype/src/types.rs :: Position::try_from_offset
    fn try_from_offset(full_offset: usize, content: &str) -> (r: Result<Self, Error>)
        ensures
            full_offset <= n(content@) ==> (r matches Ok(p) && {
                let l = line_of(content@, full_offset as int);
                p.line == l && p.character == full_offset - start(content@, l)
                    && p.character <= line_len(content@, l)
            }),
            full_offset > n(content@) ==> r is Err,
    {
        proof { axiom_rope_wf(content@); }
        let rope = Rope::from_str(content);
        let line = rope.try_char_to_line(full_offset)?;
        let character = full_offset - rope.try_line_to_char(line)?;
        Ok(Self { line, character })
    }
    // corr-end

    fn try_to_offset_orig(&self, content: &str) -> (r: Result<usize, Error>)
        ensures
            g_ok(content@, self.line as int, self.character as int)
                ==> r == Ok::<usize, Error>((start(content@, self.line as int) + self.character) as usize),
            !g_ok(content@, self.line as int, self.character as int) ==> r is Err,
            r matches Ok(o) ==> o <= n(content@),
    {
        proof { axiom_rope_wf(content@); }
        let rope = Rope::from_str(content);

        // Ropey allows line indices that are one-past-the-end, but we don't want to.
        if self.line >= rope.len_lines() {
            return Err(Error); // bail!("Position is referencing a line that doesn't exist in the content")
        }

        // Newlines are part of lines in Ropey. To make sure our character offset is
        // valid, check it against the "actual line length" (with out the optional \n).
        let line = rope.line(self.line);
        let mut line_length = line.len_chars();
        if line.chars_last_is_lf() {
            line_length -= 1;
        }

        if self.character > line_length {
            return Err(Error); // bail!("Position is referencing a character that doesn't exist in the given line")
        }

        Ok(rope.try_line_to_char(self.line)? + self.character)
    }

    // the fix, now the real code (23c37e2 / types.rs): only the `if` condition differs from try_to_offset_orig
    // corr: crates/teamtype/src/types.rs :: Position::try_to_offset
    fn try_to_offset(&self, content: &str) -> (r: Result<usize, Error>)
        ensures
            g_fixed_ok(content@, self.line as int, self.character as int)
                ==> r == Ok::<usize, Error>((start(content@, self.line as int) + self.character) as usize),
            !g_fixed_ok(content@, self.line as int, self.character as int) ==> r is Err,
            r matches Ok(o) ==> o <= n(content@),
    {
        proof { axiom_rope_wf(content@); }
        let rope = Rope::from_str(content);
        if self.line >= rope.len_lines() {
            return Err(Error);
        }
        let line = rope.line(self.line);
        let mut line_length = line.len_chars();
        if self.line + 1 < rope.len_lines() {
            line_length -= 1;
        }
        if self.character > line_length {
            return Err(Error);
        }
        Ok(rope.try_line_to_char(self.line)? + self.character)
    }
    // corr-end
}

// ---------- properties of the specs proved above ----------
proof fn line_unique(s: Seq<char>, l: int, o: int)
    requires rope_wf(s), 0 <= l < nlines(s), start(s, l) <= o <= n(s), (l == last(s) || o < start(s, l + 1)),
    ensures line_of(s, o) == l,
{
    let k = line_of(s, o);
    if k < l { assert(start(s, k + 1) <= start(s, l)) by { if k + 1 < l { assert(start(s, k + 1) < start(s, l)); } } }
    if k > l { assert(start(s, l + 1) <= start(s, k)) by { if l + 1 < k { assert(start(s, l + 1) < start(s, k)); } } }
}

// 1. offset round trip, unconditional: G(F(o)) == o
proof fn offset_round_trip(s: Seq<char>, o: int)
    requires 0 <= o <= n(s),
    ensures ({ let l = line_of(s, o); let c = o - start(s, l);
        g_ok(s, l, c) && start(s, l) + c == o && g_fixed_ok(s, l, c) }),
{
    axiom_rope_wf(s);
    let l = line_of(s, o);
    if l < last(s) { assert(start(s, l) < start(s, l + 1)); }
}

// 2. position round trip, original code: holds iff the line's terminator ends in LF
proof fn position_round_trip(s: Seq<char>, l: int, c: int)
    requires g_ok(s, l, c), l < nlines(s) - 1 ==> ends_lf(s, l),
    ensures line_of(s, start(s, l) + c) == l,
{
    axiom_rope_wf(s);
    if l < last(s) { assert(start(s, l) < start(s, l + 1)); }
    line_unique(s, l, start(s, l) + c);
}

// 2'. without the precondition the original aliases (l, len) with (l+1, 0)
proof fn position_alias(s: Seq<char>, l: int)
    requires 0 <= l < nlines(s) - 1, !ends_lf(s, l),
    ensures g_ok(s, l, line_len(s, l)), g_ok(s, l + 1, 0),
        start(s, l) + line_len(s, l) == start(s, l + 1) + 0,
{
    axiom_rope_wf(s);
    assert(start(s, l) < start(s, l + 1));
    if l + 1 < last(s) { assert(start(s, l + 1) < start(s, l + 2)); }
}

// 3. fixed code: position round trip, unconditional
proof fn position_round_trip_fixed(s: Seq<char>, l: int, c: int)
    requires g_fixed_ok(s, l, c),
    ensures line_of(s, start(s, l) + c) == l,
{
    axiom_rope_wf(s);
    if l < last(s) { assert(start(s, l) < start(s, l + 1)); }
    line_unique(s, l, start(s, l) + c);
}

// fix accepts a subset of what the original accepted (bound_fixed <= bound); equal sets on LF/CRLF text
proof fn fixed_equals_original_on_lf(s: Seq<char>, l: int, c: int)
    requires 0 <= l < nlines(s), l < nlines(s) - 1 ==> ends_lf(s, l),
    ensures g_ok(s, l, c) == g_fixed_ok(s, l, c),
{ axiom_rope_wf(s); }

// ---------- UTF-16 (MODEL of extension.ts, not the TS code) ----------
// w[i] = UTF-16 length (1 or 2) of scalar i.
pub open spec fn wf16(w: Seq<int>) -> bool { forall|i: int| 0 <= i < w.len() ==> (#[trigger] w[i] == 1 || w[i] == 2) }
// charOffsetToUTF16CodeUnitOffset
pub open spec fn u16_of(w: Seq<int>, c: int) -> int decreases c {
    if c <= 0 { 0 } else { u16_of(w, c - 1) + w[c - 1] }
}
pub open spec fn boundary(w: Seq<int>, u: int) -> bool { exists|c: int| 0 <= c <= w.len() && u16_of(w, c) == u }

proof fn u16_mono(w: Seq<int>, a: int, b: int)
    requires wf16(w), 0 <= a < b <= w.len(),
    ensures u16_of(w, a) < u16_of(w, b),
    decreases b - a,
{ if a + 1 < b { u16_mono(w, a, b - 1); } }

// injectivity of U gives C(U(c)) == c; U(C(u)) == u needs boundary(u)
proof fn u16_injective(w: Seq<int>, a: int, b: int)
    requires wf16(w), 0 <= a <= w.len(), 0 <= b <= w.len(), u16_of(w, a) == u16_of(w, b),
    ensures a == b,
{ if a < b { u16_mono(w, a, b); } if b < a { u16_mono(w, b, a); } }

proof fn u16_interior_witness()
    ensures ({ let w = seq![2int]; wf16(w) && !boundary(w, 1) }),
{
    let w = seq![2int];
    assert(w[0] == 2);
    assert(u16_of(w, 0) == 0);
    assert(u16_of(w, 1) == 2);
    assert forall|c: int| 0 <= c <= w.len() implies u16_of(w, c) != 1 by { if c == 1 { assert(u16_of(w, 1) == 2); } }
}

fn main() {}
}
