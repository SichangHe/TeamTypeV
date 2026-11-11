// Verus refinement proof of the real OT code used by teamtype:
//   operational-transform 0.6.1 (source/operational-transform-0.6.1/src/lib.rs):
//     OperationSeq::{retain, delete, insert, transform, apply}
//   teamtype (source/ot.rs): transform_through_operations, OTServer::force_apply
// Exec bodies are the source bodies with only the rewrites listed in
// REFINEMENT.md ("Assumed", rewrites); each rewritten line keeps the original as a
// `// src:` comment. Trusted items are marked ASSUMED.
use vstd::prelude::*;

verus! {

global size_of usize == 8;

// ======================= trusted string primitives (ASSUMED) =======================
// Each stands for the std/bytecount expression in its comment; `@` of a
// String/&str is its sequence of Unicode scalar values.

// src: `num_chars(s.as_bytes())` (bytecount) and `s.chars().count()`
#[verifier::external_body]
pub fn num_chars(s: &str) -> (r: usize)
    ensures r == s@.len(),
{ s.chars().count() }

// src: `s.chars()` used as an iterator
#[verifier::external_body]
pub fn chars_of(s: &str) -> (r: Vec<char>)
    ensures r@ == s@,
{ s.chars().collect() }

// src: `s.to_owned()`
#[verifier::external_body]
pub fn to_owned(s: &str) -> (r: String)
    ensures r@ == s@,
{ s.to_owned() }

// src: `*a += b` / `new_s += b`
#[verifier::external_body]
pub fn concat(a: &String, b: &str) -> (r: String)
    ensures r@ == a@ + b@,
{ let mut x = a.clone(); x.push_str(b); x }

// src: `new_s.push(c)`
#[verifier::external_body]
pub fn push_char(a: &mut String, c: char)
    ensures final(a)@ == old(a)@.push(c),
{ a.push(c) }

// src: `panic!(..)` in a branch that is proved unreachable
#[verifier::external_body]
pub fn unreachable_panic() -> !
    requires false,
{ panic!() }

// ======================= specification =======================

pub const MAXL: u64 = 0x4000_0000_0000_0000; // 2^62 characters
pub const L: u64 = 0x1000_0000_0000_0000;    // 2^60 characters

pub enum SOp { R(nat), D(nat), I(Seq<char>) }

pub open spec fn cons_of(o: SOp) -> nat { match o { SOp::R(n) => n, SOp::D(n) => n, SOp::I(_) => 0 } }
pub open spec fn prod_of(o: SOp) -> nat { match o { SOp::R(n) => n, SOp::D(_) => 0, SOp::I(s) => s.len() } }
pub open spec fn ins_of(o: SOp) -> nat { match o { SOp::I(s) => s.len(), _ => 0 } }

// characters an op sequence reads, writes, and inserts
pub open spec fn cons(p: Seq<SOp>) -> nat decreases p.len()
{ if p.len() == 0 { 0 } else { cons(p.drop_last()) + cons_of(p.last()) } }
pub open spec fn prod(p: Seq<SOp>) -> nat decreases p.len()
{ if p.len() == 0 { 0 } else { prod(p.drop_last()) + prod_of(p.last()) } }
pub open spec fn ins(p: Seq<SOp>) -> nat decreases p.len()
{ if p.len() == 0 { 0 } else { ins(p.drop_last()) + ins_of(p.last()) } }

// one op applied to exactly the text it consumes
pub open spec fn sem1(u: Seq<char>, o: SOp) -> Seq<char>
{ match o { SOp::R(_) => u, SOp::D(_) => seq![], SOp::I(s) => s } }

// meaning of an op sequence on a text of length cons(p)
pub open spec fn sem(t: Seq<char>, p: Seq<SOp>) -> Seq<char> decreases p.len()
{
    if p.len() == 0 { seq![] } else {
        let c = cons(p.drop_last());
        sem(t.take(c as int), p.drop_last()) + sem1(t.skip(c as int), p.last())
    }
}

// constructors never store Retain(0), Delete(0), or Insert("")
pub open spec fn nz(o: SOp) -> bool { match o { SOp::R(n) => n > 0, SOp::D(n) => n > 0, SOp::I(s) => s.len() > 0 } }
pub enum Operation {
    Delete(u64),
    Retain(u64),
    Insert(String),
}


pub open spec fn vop(o: Operation) -> SOp {
    match o { Operation::Delete(n) => SOp::D(n as nat), Operation::Retain(n) => SOp::R(n as nat), Operation::Insert(s) => SOp::I(s@) }
}
pub open spec fn vops(v: Seq<Operation>) -> Seq<SOp> { v.map_values(|o: Operation| vop(o)) }
pub open spec fn vopt(o: Option<Operation>) -> Seq<SOp> { match o { Some(x) => seq![vop(x)], None => seq![] } }

// ======================= lemmas =======================

pub open spec fn blank(n: int) -> Seq<char> { Seq::new(n as nat, |i: int| ' ') }


pub proof fn lemma_split(t: Seq<char>, p: Seq<SOp>, q: Seq<SOp>)
    requires t.len() == cons(p) + cons(q),
    ensures
        cons(p + q) == cons(p) + cons(q),
        prod(p + q) == prod(p) + prod(q),
        ins(p + q) == ins(p) + ins(q),
        sem(t, p + q) == sem(t.take(cons(p) as int), p) + sem(t.skip(cons(p) as int), q),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(p + q =~= p);
        assert(t.take(cons(p) as int) =~= t);
        assert(sem(t.skip(cons(p) as int), q) =~= seq![]);
    } else {
        let q0 = q.drop_last();
        assert((p + q).drop_last() =~= p + q0);
        assert((p + q).last() == q.last());
        let c = cons(p) + cons(q0);
        let t0 = t.take(c as int);
        lemma_split(t0, p, q0);
        assert(t0.take(cons(p) as int) =~= t.take(cons(p) as int));
        let u = t.skip(cons(p) as int);
        assert(u.take(cons(q0) as int) =~= t0.skip(cons(p) as int));
        assert(u.skip(cons(q0) as int) =~= t.skip(c as int));
    }
}

pub proof fn lemma_add(p: Seq<SOp>, q: Seq<SOp>)
    ensures cons(p + q) == cons(p) + cons(q), prod(p + q) == prod(p) + prod(q), ins(p + q) == ins(p) + ins(q),
{ lemma_split(blank((cons(p) + cons(q)) as int), p, q); }

pub proof fn lemma_len(t: Seq<char>, p: Seq<SOp>)
    requires t.len() == cons(p),
    ensures sem(t, p).len() == prod(p), prod(p) <= cons(p) + ins(p),
    decreases p.len(),
{
    if p.len() > 0 { lemma_len(t.take(cons(p.drop_last()) as int), p.drop_last()); }
}

pub proof fn lemma_one(t: Seq<char>, o: SOp)
    requires t.len() == cons_of(o),
    ensures cons(seq![o]) == cons_of(o), prod(seq![o]) == prod_of(o), ins(seq![o]) == ins_of(o),
            sem(t, seq![o]) == sem1(t, o),
{
    assert(seq![o].drop_last() =~= Seq::<SOp>::empty());
    reveal_with_fuel(cons, 2); reveal_with_fuel(prod, 2); reveal_with_fuel(ins, 2);
    assert(t.skip(0) =~= t);
    assert(sem(t.take(0), Seq::<SOp>::empty()) + sem1(t, o) =~= sem1(t, o));
}

// [Insert(x), Delete(k)] on a k-character text yields x
pub proof fn lemma_id(x: Seq<char>, k: nat, u: Seq<char>)
    requires u.len() == k,
    ensures ({ let qq = seq![SOp::I(x), SOp::D(k)];
        cons(qq) == k && prod(qq) == x.len() && ins(qq) == x.len() && sem(u, qq) == x }),
{
    let qq = seq![SOp::I(x), SOp::D(k)];
    assert(qq =~= seq![SOp::I(x)] + seq![SOp::D(k)]);
    lemma_one(Seq::<char>::empty(), SOp::I(x));
    lemma_one(u, SOp::D(k));
    lemma_split(u, seq![SOp::I(x)], seq![SOp::D(k)]);
    assert(u.take(0) =~= Seq::<char>::empty());
    assert(u.skip(0) =~= u);
    assert(x + seq![] =~= x);
}

pub proof fn lemma_vops_push(v: Seq<Operation>, o: Operation)
    ensures vops(v.push(o)) =~= vops(v).push(vop(o)),
{}

pub proof fn lemma_vops_update(v: Seq<Operation>, i: int, o: Operation)
    requires 0 <= i < v.len(),
    ensures vops(v.update(i, o)) =~= vops(v).update(i, vop(o)),
{}

// remaining input of one transform iterator: pending op, then the unread ops
pub open spec fn rem(ops: Seq<Operation>, mo: Option<Operation>, i: usize) -> Seq<SOp> {
    vopt(mo) + vops(ops.skip(i as int))
}

// consuming the first m characters of `r` yields `piece` (inserting `x` chars) and leaves `r2`
pub open spec fn step_ok(t: Seq<char>, r: Seq<SOp>, m: nat, piece: Seq<char>, x: nat, r2: Seq<SOp>) -> bool {
    &&& cons(r) == m + cons(r2)
    &&& prod(r) == piece.len() + prod(r2)
    &&& ins(r) == x + ins(r2)
    &&& sem(t, r) == piece + sem(t.skip(m as int), r2)
}

pub proof fn lemma_whole(t: Seq<char>, o: SOp, r: Seq<SOp>)
    requires t.len() == cons_of(o) + cons(r),
    ensures step_ok(t, seq![o] + r, cons_of(o), sem1(t.take(cons_of(o) as int), o), ins_of(o), r),
            sem1(t.take(cons_of(o) as int), o).len() == prod_of(o),
{
    lemma_one(t.take(cons_of(o) as int), o);
    lemma_split(t, seq![o], r);
}

pub proof fn lemma_part(t: Seq<char>, o: SOp, m: nat, r: Seq<SOp>)
    requires t.len() == cons_of(o) + cons(r), !(o is I), 0 < m < cons_of(o),
    ensures ({
        let (om, rest) = match o { SOp::R(j) => (SOp::R(m), SOp::R((j - m) as nat)), _ => (SOp::D(m), SOp::D((cons_of(o) - m) as nat)) };
        step_ok(t, seq![o] + r, m, sem1(t.take(m as int), om), 0, seq![rest] + r)
        && sem1(t.take(m as int), om).len() == prod_of(om) && nz(rest)
    }),
{
    let (om, rest) = match o { SOp::R(j) => (SOp::R(m), SOp::R((j - m) as nat)), _ => (SOp::D(m), SOp::D((cons_of(o) - m) as nat)) };
    lemma_whole(t, o, r);
    let u = t.skip(m as int);
    lemma_whole(u, rest, r);
    lemma_one(t.take(m as int), om);
    assert(u.take(cons_of(rest) as int) =~= t.take(cons_of(o) as int).skip(m as int));
    assert(u.skip(cons_of(rest) as int) =~= t.skip(cons_of(o) as int));
    assert(t.take(cons_of(o) as int) =~= t.take(m as int) + u.take(cons_of(rest) as int));
    let tail = sem(t.skip(cons_of(o) as int), r);
    if o is R {
        assert(sem(t, seq![o] + r) =~= t.take(m as int) + (u.take(cons_of(rest) as int) + tail));
    } else {
        assert(sem(t, seq![o] + r) =~= seq![] + (seq![] + tail));
        assert(sem(u, seq![rest] + r) =~= seq![] + tail);
    }
}

pub proof fn lemma_next(ops: Seq<Operation>, i: usize, mo: Option<Operation>, j: usize)
    requires
        i <= ops.len(),
        i < ops.len() ==> j == i + 1 && mo is Some && vop(mo->Some_0) == vop(ops[i as int]),
        i == ops.len() ==> j == i && mo is None,
    ensures vops(ops.skip(i as int)) == rem(ops, mo, j),
{
    if i < ops.len() {
        assert(vops(ops.skip(i as int)) =~= seq![vop(ops[i as int])] + vops(ops.skip(j as int)));
    } else {
        assert(vops(ops.skip(i as int)) =~= Seq::<SOp>::empty());
        assert(rem(ops, mo, j) =~= Seq::<SOp>::empty());
    }
}

pub proof fn lemma_rem_some(ops: Seq<Operation>, o: Operation, i: usize)
    ensures rem(ops, Some(o), i) =~= seq![vop(o)] + vops(ops.skip(i as int)),
{}

pub proof fn lemma_nz_skip(ops: Seq<Operation>, i: usize)
    requires i <= ops.len(), forall|j: int| 0 <= j < vops(ops).len() ==> nz(#[trigger] vops(ops)[j]),
    ensures forall|j: int| 0 <= j < vops(ops.skip(i as int)).len() ==> nz(#[trigger] vops(ops.skip(i as int))[j]),
{
    assert forall|j: int| 0 <= j < vops(ops.skip(i as int)).len() implies nz(#[trigger] vops(ops.skip(i as int))[j]) by {
        assert(vops(ops.skip(i as int))[j] == vops(ops)[j + i]);
    }
}

pub proof fn lemma_vops_skip0(ops: Seq<Operation>)
    ensures vops(ops.skip(0)) =~= vops(ops),
{ assert(ops.skip(0) =~= ops); }

pub proof fn lemma_adv_whole(ops: Seq<Operation>, o: Operation, i: usize, mo: Option<Operation>, j: usize, t: Seq<char>)
    requires
        i <= ops.len(),
        i < ops.len() ==> j == i + 1 && mo is Some && vop(mo->Some_0) == vop(ops[i as int]),
        i == ops.len() ==> j == i && mo is None,
        t.len() == cons(rem(ops, Some(o), i)),
    ensures
        step_ok(t, rem(ops, Some(o), i), cons_of(vop(o)), sem1(t.take(cons_of(vop(o)) as int), vop(o)), ins_of(vop(o)), rem(ops, mo, j)),
        sem1(t.take(cons_of(vop(o)) as int), vop(o)).len() == prod_of(vop(o)),
{
    lemma_rem_some(ops, o, i);
    lemma_next(ops, i, mo, j);
    lemma_one(blank(cons_of(vop(o)) as int), vop(o));
    lemma_add(seq![vop(o)], vops(ops.skip(i as int)));
    lemma_whole(t, vop(o), vops(ops.skip(i as int)));
}

pub proof fn lemma_adv_part(ops: Seq<Operation>, o: Operation, i: usize, o2: Operation, m: nat, t: Seq<char>)
    requires
        t.len() == cons(rem(ops, Some(o), i)), !(o is Insert), 0 < m < cons_of(vop(o)),
        vop(o2) == (match vop(o) { SOp::R(j) => SOp::R((j - m) as nat), _ => SOp::D((cons_of(vop(o)) - m) as nat) }),
    ensures ({
        let om = match vop(o) { SOp::R(_) => SOp::R(m), _ => SOp::D(m) };
        step_ok(t, rem(ops, Some(o), i), m, sem1(t.take(m as int), om), 0, rem(ops, Some(o2), i))
        && sem1(t.take(m as int), om).len() == prod_of(om) && nz(vop(o2))
    }),
{
    lemma_rem_some(ops, o, i);
    lemma_rem_some(ops, o2, i);
    lemma_one(blank(cons_of(vop(o)) as int), vop(o));
    lemma_add(seq![vop(o)], vops(ops.skip(i as int)));
    lemma_part(t, vop(o), m, vops(ops.skip(i as int)));
}

// ======================= real code: teamtype source/types.rs conversions =======================

pub enum TextOp {
    Retain(usize),
    Insert(String),
    Delete(usize),
}

pub struct TextDelta(pub Vec<TextOp>);

pub open spec fn tvop(o: TextOp) -> SOp {
    match o { TextOp::Retain(n) => SOp::R(n as nat), TextOp::Delete(n) => SOp::D(n as nat), TextOp::Insert(s) => SOp::I(s@) }
}
pub open spec fn tvops(v: Seq<TextOp>) -> Seq<SOp> { v.map_values(|o: TextOp| tvop(o)) }

pub fn clone_text_op(o: &TextOp) -> (r: TextOp) ensures tvop(r) == tvop(*o),
{ match o { TextOp::Retain(n) => TextOp::Retain(*n), TextOp::Insert(s) => TextOp::Insert(s.clone()), TextOp::Delete(n) => TextOp::Delete(*n) } }

impl TextDelta {
    pub open spec fn v(&self) -> Seq<SOp> { tvops(self.0@) }

    // src: `#[derive(Default)]`
    pub fn default() -> (r: Self) ensures r.v() == Seq::<SOp>::empty(),
    { let r = TextDelta(Vec::new()); assert(r.v() =~= Seq::<SOp>::empty()); r }

    pub fn retain(&mut self, n: usize)
        ensures final(self).v() == (if n != 0 { old(self).v().push(SOp::R(n as nat)) } else { old(self).v() }),
    {
        if n != 0 {
            self.0.push(TextOp::Retain(n));
            proof { assert(self.v() =~= old(self).v().push(SOp::R(n as nat))); }
        }
    }

    pub fn insert(&mut self, s: &str)
        ensures final(self).v() == (if s@.len() != 0 { old(self).v().push(SOp::I(s@)) } else { old(self).v() }),
    {
        if num_chars(s) != 0 { // src: `!s.is_empty()`
            self.0.push(TextOp::Insert(to_owned(s))); // src: `s.to_string()`
            proof { assert(self.v() =~= old(self).v().push(SOp::I(s@))); }
        }
    }

    pub fn delete(&mut self, n: usize)
        ensures final(self).v() == (if n != 0 { old(self).v().push(SOp::D(n as nat)) } else { old(self).v() }),
    {
        if n != 0 {
            self.0.push(TextOp::Delete(n));
            proof { assert(self.v() =~= old(self).v().push(SOp::D(n as nat))); }
        }
    }

    // src: `#[derive(Clone)]`
    pub fn clone_delta(&self) -> (r: Self) ensures r.v() == self.v(),
    {
        let mut v: Vec<TextOp> = Vec::new();
        let mut i: usize = 0;
        while i < self.0.len()
            invariant i <= self.0@.len(), tvops(v@) == tvops(self.0@.take(i as int)),
            decreases self.0@.len() - i,
        {
            let o = clone_text_op(&self.0[i]);
            proof {
                assert(self.0@.take(i + 1) =~= self.0@.take(i as int).push(self.0@[i as int]));
                assert(tvops(v@.push(o)) =~= tvops(v@).push(tvop(o)));
                assert(tvops(self.0@.take(i + 1)) =~= tvops(self.0@.take(i as int)).push(tvop(self.0@[i as int])));
            }
            v.push(o);
            i += 1;
        }
        proof { assert(self.0@.take(i as int) =~= self.0@); }
        TextDelta(v)
    }
}

// ======================= Ropey line model (concrete definition) =======================
// ASSUMED (see CONTRACTS.md): Ropey 1.6.1 splits text into lines exactly as defined here.
// A line starts at 0 and just after every line break, where line breaks are
// LF, VT, FF, CR, NEL (U+85), LS (U+2028), PS (U+2029), except that CR followed by LF is one break.
// Characters are Unicode scalar values (Rust `char`).

pub open spec fn brk(c: char) -> bool {
    let u = c as u32;
    u == 0xA || u == 0xB || u == 0xC || u == 0xD || u == 0x85 || u == 0x2028 || u == 0x2029
}

// p is the first character offset of some line (0 <= p <= s.len())
pub open spec fn is_start(s: Seq<char>, p: int) -> bool {
    p == 0 || (brk(s[p - 1]) && !((s[p - 1] as u32) == 0xD && p < s.len() && (s[p] as u32) == 0xA))
}

// the line starts at offsets <= p, in increasing order
pub open spec fn starts(s: Seq<char>, p: int) -> Seq<int> decreases p {
    if p <= 0 { seq![0int] } else if is_start(s, p) { starts(s, p - 1).push(p) } else { starts(s, p - 1) }
}

pub open spec fn n(s: Seq<char>) -> int { s.len() as int }
pub open spec fn nlines(s: Seq<char>) -> int { starts(s, n(s)).len() as int }
pub open spec fn start(s: Seq<char>, l: int) -> int { starts(s, n(s))[l] }       // Rope::line_to_char
pub open spec fn line_of(s: Seq<char>, o: int) -> int { starts(s, o).len() - 1 }  // Rope::char_to_line
pub open spec fn last(s: Seq<char>) -> int { nlines(s) - 1 }
// length of line l in chars, including its terminator
pub open spec fn line_len(s: Seq<char>, l: int) -> int {
    if l < last(s) { start(s, l + 1) - start(s, l) } else { n(s) - start(s, l) }
}

proof fn lemma_starts_basic(s: Seq<char>, p: int)
    requires 0 <= p,
    ensures
        starts(s, p).len() >= 1,
        starts(s, p).len() <= p + 1,
        starts(s, p)[0] == 0,
        forall|i: int| 0 <= i < starts(s, p).len() ==> 0 <= #[trigger] starts(s, p)[i] <= p,
        forall|i: int, j: int| 0 <= i < j < starts(s, p).len() ==> #[trigger] starts(s, p)[i] < #[trigger] starts(s, p)[j],
    decreases p,
{
    if p > 0 {
        lemma_starts_basic(s, p - 1);
        let r = starts(s, p - 1);
        if is_start(s, p) {
            let st = r.push(p);
            assert forall|i: int| 0 <= i < st.len() implies 0 <= #[trigger] st[i] <= p by {
                if i < r.len() { assert(st[i] == r[i]); }
            }
            assert forall|i: int, j: int| 0 <= i < j < st.len() implies #[trigger] st[i] < #[trigger] st[j] by {
                if j < r.len() { assert(st[i] == r[i] && st[j] == r[j]); } else { assert(st[i] == r[i]); }
            }
        }
    }
}

// starts(s, p) is a prefix of starts(s, q), and the rest of starts(s, q) is beyond p
proof fn lemma_starts_ext(s: Seq<char>, p: int, q: int)
    requires 0 <= p <= q,
    ensures
        starts(s, p).len() <= starts(s, q).len(),
        forall|i: int| 0 <= i < starts(s, p).len() ==> #[trigger] starts(s, q)[i] == starts(s, p)[i],
        forall|k: int| starts(s, p).len() <= k < starts(s, q).len() ==> #[trigger] starts(s, q)[k] > p,
    decreases q - p,
{
    if q > p {
        lemma_starts_ext(s, p, q - 1);
        lemma_starts_basic(s, q - 1);
        if is_start(s, q) {
            let r = starts(s, q - 1);
            let st = r.push(q);
            assert forall|i: int| 0 <= i < starts(s, p).len() implies #[trigger] st[i] == starts(s, p)[i] by {
                assert(st[i] == r[i]);
            }
            assert forall|k: int| starts(s, p).len() <= k < st.len() implies #[trigger] st[k] > p by {
                if k < r.len() { assert(st[k] == r[k]); }
            }
        }
    }
}

// the facts every user of the line model needs
proof fn lemma_lines(s: Seq<char>)
    ensures
        nlines(s) >= 1,
        nlines(s) <= n(s) + 1,
        start(s, 0) == 0,
        forall|l: int| 0 <= l < nlines(s) ==> 0 <= #[trigger] start(s, l) <= n(s),
        forall|i: int, j: int| 0 <= i < j < nlines(s) ==> #[trigger] start(s, i) < #[trigger] start(s, j),
        forall|o: int| 0 <= o <= n(s) ==> {
            let l = #[trigger] line_of(s, o);
            &&& 0 <= l < nlines(s)
            &&& start(s, l) <= o
            &&& (l + 1 < nlines(s) ==> o < start(s, l + 1))
            &&& l <= o
        },
        forall|o1: int, o2: int| 0 <= o1 <= o2 <= n(s) ==> #[trigger] line_of(s, o1) <= #[trigger] line_of(s, o2),
{
    lemma_starts_basic(s, n(s));
    assert forall|o: int| 0 <= o <= n(s) implies ({
            let l = #[trigger] line_of(s, o);
            &&& 0 <= l < nlines(s)
            &&& start(s, l) <= o
            &&& (l + 1 < nlines(s) ==> o < start(s, l + 1))
            &&& l <= o
        }) by {
        lemma_starts_basic(s, o);
        lemma_starts_ext(s, o, n(s));
        let l = line_of(s, o);
        assert(start(s, l) == starts(s, o)[l]);
    }
    assert forall|o1: int, o2: int| 0 <= o1 <= o2 <= n(s) implies #[trigger] line_of(s, o1) <= #[trigger] line_of(s, o2) by {
        lemma_starts_ext(s, o1, o2);
    }
}

// ---------- position <-> offset: specification ----------
// valid position: Position::try_to_offset accepts it
pub open spec fn bound(s: Seq<char>, l: int) -> int {
    line_len(s, l) - if l < last(s) { 1int } else { 0int }
}
pub open spec fn valid(s: Seq<char>, l: int, c: int) -> bool { 0 <= l < nlines(s) && 0 <= c <= bound(s, l) }
pub open spec fn gof(s: Seq<char>, l: int, c: int) -> int { start(s, l) + c }  // position -> offset

// F then G is the identity on offsets, for every offset 0..=N, with a valid position in between
proof fn lemma_offset_rt(s: Seq<char>, o: int)
    requires 0 <= o <= n(s),
    ensures ({
        let l = line_of(s, o);
        let c = o - start(s, l);
        &&& valid(s, l, c)
        &&& gof(s, l, c) == o
        &&& 0 <= c <= line_len(s, l)
    }),
{
    lemma_lines(s);
}

// G then F is the identity on valid positions
proof fn lemma_pos_rt(s: Seq<char>, l: int, c: int)
    requires valid(s, l, c),
    ensures n(s) >= gof(s, l, c) >= 0, gof(s, l, c) <= n(s), line_of(s, gof(s, l, c)) == l,
{
    lemma_lines(s);
    let o = gof(s, l, c);
    if l < last(s) { assert(start(s, l) < start(s, l + 1)); }
    let l2 = line_of(s, o);
    if l2 > l {
        assert(start(s, l + 1) <= start(s, l2)) by { if l + 1 < l2 { assert(start(s, l + 1) < start(s, l2)); } }
    }
    if l2 < l {
        assert(start(s, l2 + 1) <= start(s, l)) by { if l2 + 1 < l { assert(start(s, l2 + 1) < start(s, l)); } }
    }
}

// G is strictly increasing in the lexicographic order of positions
proof fn lemma_g_mono(s: Seq<char>, l1: int, c1: int, l2: int, c2: int)
    requires valid(s, l1, c1), valid(s, l2, c2), l1 < l2 || (l1 == l2 && c1 < c2),
    ensures gof(s, l1, c1) < gof(s, l2, c2),
{
    lemma_lines(s);
    if l1 < l2 {
        assert(start(s, l1) < start(s, l1 + 1));
        assert(start(s, l1 + 1) <= start(s, l2)) by { if l1 + 1 < l2 { assert(start(s, l1 + 1) < start(s, l2)); } }
    }
}

pub open spec fn fwd(l1: int, c1: int, l2: int, c2: int) -> bool { l1 < l2 || (l1 == l2 && c1 <= c2) }

// for valid positions, "forward" is exactly "offset order"
proof fn lemma_fwd_iff(s: Seq<char>, l1: int, c1: int, l2: int, c2: int)
    requires valid(s, l1, c1), valid(s, l2, c2),
    ensures
        fwd(l1, c1, l2, c2) ==> gof(s, l1, c1) <= gof(s, l2, c2),
        !fwd(l1, c1, l2, c2) ==> gof(s, l2, c2) < gof(s, l1, c1),
{
    if fwd(l1, c1, l2, c2) {
        if l1 == l2 && c1 == c2 {} else { lemma_g_mono(s, l1, c1, l2, c2); }
    } else {
        lemma_g_mono(s, l2, c2, l1, c1);
    }
}

// F is monotone, so F(a) <= F(b) lexicographically when a <= b
proof fn lemma_f_fwd(s: Seq<char>, a: int, b: int)
    requires 0 <= a <= b <= n(s),
    ensures ({
        let la = line_of(s, a); let lb = line_of(s, b);
        fwd(la, a - start(s, la), lb, b - start(s, lb))
    }),
{
    lemma_lines(s);
}

// ASSUMED: a Rust `&str` has at most usize::MAX characters (it has at most isize::MAX bytes).
#[verifier::external_body]
pub proof fn axiom_str_len(s: &str)
    ensures s@.len() <= usize::MAX,
{}

// ======================= trusted Ropey primitives (ASSUMED; contracts for ropey_proof) =======================
pub struct Error;

#[verifier::external_body]
pub struct Rope { inner: () }
#[verifier::external_body]
pub struct RopeSlice { inner: () }

impl Rope {
    pub uninterp spec fn view(&self) -> Seq<char>;

    // src: `Rope::from_str(content)`
    #[verifier::external_body]
    pub fn from_str(content: &str) -> (r: Rope)
        ensures r@ == content@,
    { unimplemented!() }

    // src: `rope.len_lines()`
    #[verifier::external_body]
    pub fn len_lines(&self) -> (r: usize)
        ensures r as int == nlines(self@),
    { unimplemented!() }

    // src: `rope.try_char_to_line(o)`
    #[verifier::external_body]
    pub fn try_char_to_line(&self, o: usize) -> (r: Result<usize, Error>)
        ensures
            o <= n(self@) ==> r == Ok::<usize, Error>(line_of(self@, o as int) as usize),
            o > n(self@) ==> r is Err,
    { unimplemented!() }

    // src: `rope.try_line_to_char(l)`; Ropey accepts the one-past-the-end line index
    #[verifier::external_body]
    pub fn try_line_to_char(&self, l: usize) -> (r: Result<usize, Error>)
        ensures
            l < nlines(self@) ==> r == Ok::<usize, Error>(start(self@, l as int) as usize),
            l == nlines(self@) ==> r == Ok::<usize, Error>(n(self@) as usize),
            l > nlines(self@) ==> r is Err,
    { unimplemented!() }

    // src: `rope.line(l)`
    #[verifier::external_body]
    pub fn line(&self, l: usize) -> (r: RopeSlice)
        requires l < nlines(self@),
        ensures r.len() == line_len(self@, l as int),
    { unimplemented!() }
}

impl RopeSlice {
    pub uninterp spec fn len(&self) -> int;

    // src: `line.len_chars()`
    #[verifier::external_body]
    pub fn len_chars(&self) -> (r: usize)
        ensures r as int == self.len(),
    { unimplemented!() }
}

// ======================= real code: types.rs, Position / Range =======================

#[derive(PartialEq, Eq)]
pub struct Position { pub line: usize, pub character: usize }

impl Position {
    pub open spec fn ok(&self, s: Seq<char>) -> bool { valid(s, self.line as int, self.character as int) }
    pub open spec fn off(&self, s: Seq<char>) -> int { gof(s, self.line as int, self.character as int) }

    // corr: crates/teamtype/src/types.rs :: Position::try_from_offset
    // src: `fn try_from_offset(full_offset: usize, content: &str) -> Result<Self>`
    pub fn try_from_offset(full_offset: usize, content: &str) -> (r: Result<Self, Error>)
        ensures
            full_offset <= content@.len() ==> (r matches Ok(p) && p.ok(content@) && p.off(content@) == full_offset),
            full_offset > content@.len() ==> r is Err,
    {
        proof { axiom_str_len(content); lemma_lines(content@); if full_offset <= content@.len() { lemma_offset_rt(content@, full_offset as int); } }
        let rope = Rope::from_str(content);
        // src: `let line = rope.try_char_to_line(full_offset)?;`
        let line = match rope.try_char_to_line(full_offset) { Ok(l) => l, Err(e) => return Err(e) };
        // src: `let character = full_offset - rope.try_line_to_char(line)?;`
        let st = match rope.try_line_to_char(line) { Ok(x) => x, Err(e) => return Err(e) };
        let character = full_offset - st;
        Ok(Self { line, character })
    }
    // corr-end

    // corr: crates/teamtype/src/types.rs :: Position::try_to_offset
    // src: `fn try_to_offset(&self, content: &str) -> Result<usize>`
    pub fn try_to_offset(&self, content: &str) -> (r: Result<usize, Error>)
        ensures
            self.ok(content@) ==> r == Ok::<usize, Error>(self.off(content@) as usize),
            !self.ok(content@) ==> r is Err,
            r matches Ok(o) ==> o <= content@.len(),
    {
        proof { axiom_str_len(content); lemma_lines(content@); }
        let rope = Rope::from_str(content);
        proof { if self.ok(content@) { lemma_pos_rt(content@, self.line as int, self.character as int); } }

        // src: `if self.line >= rope.len_lines() { bail!(..) }`
        if self.line >= rope.len_lines() {
            return Err(Error);
        }

        let line = rope.line(self.line);
        let mut line_length = line.len_chars();
        // src: `if self.line + 1 < rope.len_lines() { line_length -= 1; }`
        if self.line + 1 < rope.len_lines() {
            proof { assert(start(content@, self.line as int) < start(content@, self.line as int + 1)); }
            line_length -= 1;
        }

        // src: `if self.character > line_length { bail!(..) }`
        if self.character > line_length {
            return Err(Error);
        }

        // src: `Ok(rope.try_line_to_char(self.line)? + self.character)`
        proof { assert(self.ok(content@)); lemma_pos_rt(content@, self.line as int, self.character as int); }
        let st = match rope.try_line_to_char(self.line) { Ok(x) => x, Err(e) => return Err(e) };
        Ok(st + self.character)
    }
    // corr-end
}

pub struct Range { pub start: Position, pub end: Position }

impl Range {
    // src: `pub fn is_empty(&self) -> bool { self.start == self.end }` (derived PartialEq written out)
    pub fn is_empty(&self) -> (r: bool)
        ensures r == (self.start.line == self.end.line && self.start.character == self.end.character),
    {
        self.start.line == self.end.line && self.start.character == self.end.character
    }

    pub open spec fn forward(&self) -> bool {
        fwd(self.start.line as int, self.start.character as int, self.end.line as int, self.end.character as int)
    }

    // src: `pub fn is_forward(&self) -> bool`
    pub fn is_forward(&self) -> (r: bool)
        ensures r == self.forward(),
    {
        (self.start.line < self.end.line)
            || (self.start.line == self.end.line && self.start.character <= self.end.character)
    }

    // corr: crates/teamtype/src/types.rs :: Range::as_relative
    // src: `pub fn as_relative(&self, content: &str) -> Result<(usize, usize)>`
    pub fn as_relative(&self, content: &str) -> (r: Result<(usize, usize), Error>)
        ensures
            (self.start.ok(content@) && self.end.ok(content@)) ==> (r matches Ok((p, len)) && {
                let a = self.start.off(content@); let b = self.end.off(content@);
                &&& p == (if a <= b { a } else { b })
                &&& len == (if a <= b { b - a } else { a - b })
                &&& p + len <= content@.len()
                &&& (self.forward() <==> a <= b)
            }),
            !(self.start.ok(content@) && self.end.ok(content@)) ==> r is Err,
    {
        // src: `self.start.try_to_offset(content).context(..)?`
        let start_offset = match self.start.try_to_offset(content) { Ok(o) => o, Err(e) => return Err(e) };
        // src: `self.end.try_to_offset(content).context(..)?`
        let end_offset = match self.end.try_to_offset(content) { Ok(o) => o, Err(e) => return Err(e) };
        proof {
            assert(self.start.ok(content@) && self.end.ok(content@));
            axiom_str_len(content);
            lemma_pos_rt(content@, self.start.line as int, self.start.character as int);
            lemma_pos_rt(content@, self.end.line as int, self.end.character as int);
            lemma_fwd_iff(content@, self.start.line as int, self.start.character as int, self.end.line as int, self.end.character as int);
        }
        if self.is_forward() {
            Ok((start_offset, end_offset - start_offset))
        } else {
            Ok((end_offset, start_offset - end_offset))
        }
    }
    // corr-end
}

// ======================= delta <-> editor-op semantics =======================

// force_apply semantics: apply to the first cons(p) characters, keep the rest
pub open spec fn fsem(t: Seq<char>, p: Seq<SOp>) -> Seq<char> {
    sem(t.take(cons(p) as int), p) + t.skip(cons(p) as int)
}

// An editor operation, abstracted to character offsets: replace [a, b) by r.
pub struct Trip { pub a: int, pub b: int, pub r: Seq<char> }

// the editor ops that `EditorTextDelta::try_from_delta` makes for an op sequence, as offsets
// into the ORIGINAL text (Retain emits nothing, Delete a deletion, Insert an empty-range insertion)
pub open spec fn ed_of(p: Seq<SOp>) -> Seq<Trip> decreases p.len() {
    if p.len() == 0 { seq![] } else {
        let q = p.drop_last();
        let pos = cons(q) as int;
        ed_of(q) + match p.last() {
            SOp::R(_) => seq![],
            SOp::D(k) => seq![Trip { a: pos, b: pos + k, r: seq![] }],
            SOp::I(x) => seq![Trip { a: pos, b: pos, r: x }],
        }
    }
}

// replace c[at, at+del) by r
pub open spec fn splice(c: Seq<char>, at: int, del: int, r: Seq<char>) -> Seq<char> {
    c.take(at) + r + c.skip(at + del)
}

// total length change of a list of replacements
pub open spec fn osum(e: Seq<Trip>) -> int decreases e.len() {
    if e.len() == 0 { 0 } else { osum(e.drop_last()) + e.last().r.len() - (e.last().b - e.last().a) }
}

// document.rs: apply the replacements in order; each one's start (an original offset) is shifted
// by the net length change of the earlier ones
pub open spec fn run(orig: Seq<char>, e: Seq<Trip>) -> Seq<char> decreases e.len() {
    if e.len() == 0 { orig } else {
        let t = e.last();
        splice(run(orig, e.drop_last()), t.a + osum(e.drop_last()), t.b - t.a, t.r)
    }
}

proof fn lemma_push_unfold(t: Seq<char>, q: Seq<SOp>, o: SOp)
    ensures
        cons(q.push(o)) == cons(q) + cons_of(o),
        prod(q.push(o)) == prod(q) + prod_of(o),
        ins(q.push(o)) == ins(q) + ins_of(o),
        sem(t, q.push(o)) == sem(t.take(cons(q) as int), q) + sem1(t.skip(cons(q) as int), o),
{
    assert(q.push(o).drop_last() =~= q);
    assert(q.push(o).last() == o);
}

proof fn lemma_cons_prefix(p: Seq<SOp>, m: int)
    requires 0 <= m <= p.len(),
    ensures
        cons(p.take(m)) <= cons(p),
        ins(p.take(m)) <= ins(p),
{
    assert(p =~= p.take(m) + p.skip(m));
    lemma_add(p.take(m), p.skip(m));
}

proof fn lemma_fsem_push(t: Seq<char>, q: Seq<SOp>, o: SOp)
    requires cons(q) + cons_of(o) <= t.len(),
    ensures ({
        let cq = cons(q) as int; let k = cons_of(o) as int;
        &&& cons(q.push(o)) == cq + k
        &&& fsem(t, q.push(o)) == sem(t.take(cq), q) + sem1(t.skip(cq).take(k), o) + t.skip(cq + k)
    }),
{
    let cq = cons(q) as int; let k = cons_of(o) as int;
    lemma_push_unfold(t.take(cq + k), q, o);
    assert(t.take(cq + k).take(cq) =~= t.take(cq));
    assert(t.take(cq + k).skip(cq) =~= t.skip(cq).take(k));
}

#[verifier::spinoff_prover]
proof fn lemma_run_step(orig: Seq<char>, q: Seq<SOp>, o: SOp)
    requires cons(q) + cons_of(o) <= orig.len(),
    ensures ({
        let p = q.push(o);
        let cq = cons(q) as int;
        &&& cons(p) == cq + cons_of(o)
        &&& (run(orig, ed_of(q)) == fsem(orig, q) && osum(ed_of(q)) == prod(q) as int - cq
            ==> run(orig, ed_of(p)) == fsem(orig, p) && osum(ed_of(p)) == prod(p) as int - cons(p) as int)
    }),
{
    let p = q.push(o);
    assert(p.drop_last() =~= q);
    assert(p.last() == o);
    lemma_push_unfold(blank(cons(p) as int), q, o);
    let cq = cons(q) as int;
    lemma_fsem_push(orig, q, o);
    lemma_len(orig.take(cq), q);
    let x = sem(orig.take(cq), q);
    let pq = prod(q) as int;
    let rest = orig.skip(cq);
    let cur = x + rest;
    assert(x.len() == pq);
    if run(orig, ed_of(q)) == fsem(orig, q) && osum(ed_of(q)) == prod(q) as int - cq {
        assert(fsem(orig, q) == cur);
        match o {
            SOp::R(k) => {
                assert(ed_of(p) =~= ed_of(q));
                assert(rest =~= rest.take(k as int) + orig.skip(cq + k));
            }
            SOp::D(k) => {
                let t = Trip { a: cq, b: cq + k, r: seq![] };
                assert(ed_of(p) =~= ed_of(q).push(t));
                assert(ed_of(p).drop_last() =~= ed_of(q));
                assert(ed_of(p).last() == t);
                assert(cur.take(pq) =~= x);
                assert(cur.skip(pq + k) =~= orig.skip(cq + k));
            }
            SOp::I(y) => {
                let t = Trip { a: cq, b: cq, r: y };
                assert(ed_of(p) =~= ed_of(q).push(t));
                assert(ed_of(p).drop_last() =~= ed_of(q));
                assert(ed_of(p).last() == t);
                assert(cur.take(pq) =~= x);
                assert(cur.skip(pq) =~= rest);
            }
        }
    }
}

proof fn lemma_run_fsem(orig: Seq<char>, p: Seq<SOp>)
    requires cons(p) <= orig.len(),
    ensures
        run(orig, ed_of(p)) == fsem(orig, p),
        osum(ed_of(p)) == prod(p) as int - cons(p) as int,
    decreases p.len(),
{
    if p.len() == 0 {
        assert(orig.take(0) =~= Seq::<char>::empty());
        assert(orig.skip(0) =~= orig);
        assert(sem(orig.take(0), p) =~= Seq::<char>::empty());
        assert(fsem(orig, p) =~= orig);
    } else {
        let q = p.drop_last();
        let o = p.last();
        assert(p =~= q.push(o));
        lemma_push_unfold(blank(cons(p) as int), q, o);
        lemma_run_fsem(orig, q);
        lemma_run_step(orig, q, o);
    }
}

// ======================= conversion + apply: real try_from_delta / apply_delta_to_doc =======================

// the trusted Automerge `splice_text` on a char buffer (ASSUMED): in range it replaces
// doc[at, at+del) by r; the real call is `.expect(..)`ed, so out-of-range would panic and
// is excluded by the precondition (proved at the call site)
#[verifier::external_body]
pub fn splice_chars(doc: &mut Vec<char>, at: usize, del: usize, r: &str)
    requires at + del <= old(doc)@.len(),
    ensures final(doc)@ == splice(old(doc)@, at as int, del as int, r@),
{ let rr: Vec<char> = r.chars().collect(); doc.splice(at..at + del, rr); }

// src: `String` built from the doc's characters (`text`/`current_file_content` read-back)
#[verifier::external_body]
pub fn string_of(v: &Vec<char>) -> (r: String)
    ensures r@ == v@,
{ v.iter().collect() }

pub struct EditorTextOp { pub range: Range, pub replacement: String }
pub struct EditorTextDelta(pub Vec<EditorTextOp>);

// the exec editor ops decode, on `c`, to exactly the offset triples `t`
pub open spec fn decodes(d: Seq<EditorTextOp>, c: Seq<char>, t: Seq<Trip>) -> bool {
    &&& d.len() == t.len()
    &&& forall|j: int| 0 <= j < d.len() ==> {
        &&& (#[trigger] d[j]).range.start.ok(c) && d[j].range.start.off(c) == t[j].a
        &&& d[j].range.end.ok(c) && d[j].range.end.off(c) == t[j].b
        &&& d[j].replacement@ == t[j].r
    }
}

proof fn lemma_ed_unfold(q: Seq<SOp>, o: SOp)
    ensures ed_of(q.push(o)) == ed_of(q) + match o {
            SOp::R(_) => seq![],
            SOp::D(k) => seq![Trip { a: cons(q) as int, b: cons(q) as int + k, r: seq![] }],
            SOp::I(x) => seq![Trip { a: cons(q) as int, b: cons(q) as int, r: x }],
        },
{
    let p = q.push(o);
    assert(p.drop_last() =~= q);
    assert(p.last() == o);
}

// the j-th replacement is produced by one op p[m]; the replacements before it are those of p[..m]
proof fn lemma_ed_split(p: Seq<SOp>, j: int)
    requires 0 <= j < ed_of(p).len(),
    ensures exists|m: int| 0 <= m < p.len() && #[trigger] ed_of(p.take(m)) =~= ed_of(p).take(j)
        && ed_of(p.take(m + 1)) =~= ed_of(p).take(j + 1),
    decreases p.len(),
{
    let q = p.drop_last();
    let o = p.last();
    assert(p =~= q.push(o));
    lemma_ed_unfold(q, o);
    if j < ed_of(q).len() {
        lemma_ed_split(q, j);
        let m = choose|m: int| 0 <= m < q.len() && #[trigger] ed_of(q.take(m)) =~= ed_of(q).take(j)
            && ed_of(q.take(m + 1)) =~= ed_of(q).take(j + 1);
        assert(q.take(m) =~= p.take(m));
        assert(q.take(m + 1) =~= p.take(m + 1));
        assert(ed_of(p).take(j) =~= ed_of(q).take(j));
        assert(ed_of(p).take(j + 1) =~= ed_of(q).take(j + 1));
    } else {
        let m = q.len() as int;
        assert(p.take(m) =~= q);
        assert(p.take(m + 1) =~= p);
        assert(j == ed_of(q).len());
        assert(ed_of(p).take(j) =~= ed_of(q));
        assert(ed_of(p).take(j + 1) =~= ed_of(p));
    }
}

proof fn lemma_off_le(c: Seq<char>, p: Position)
    requires p.ok(c),
    ensures p.off(c) <= c.len(),
{ lemma_lines(c); lemma_pos_rt(c, p.line as int, p.character as int); }

// corr: crates/teamtype/src/types.rs :: EditorTextDelta::try_from_delta
// src: `EditorTextDelta::try_from_delta(delta: TextDelta, content: &str) -> Result<Self>`
pub fn try_from_delta(delta: TextDelta, content: &str) -> (r: Result<EditorTextDelta, Error>)
    requires cons(delta.v()) <= MAXL,
    ensures
        r matches Ok(d) ==> decodes(d.0@, content@, ed_of(delta.v())),
        cons(delta.v()) <= content@.len() ==> r is Ok,
{
    let ghost p0 = delta.v();
    let mut editor_ops: Vec<EditorTextOp> = Vec::new();
    let mut position: usize = 0;
    // src: `for op in delta`
    let mut i: usize = 0;
    proof { assert(tvops(delta.0@.take(0)) =~= Seq::<SOp>::empty()); axiom_str_len(content); }
    while i < delta.0.len()
        invariant
            i <= delta.0@.len(), cons(p0) <= MAXL, p0 == delta.v(),
            position == cons(tvops(delta.0@.take(i as int))),
            decodes(editor_ops@, content@, ed_of(tvops(delta.0@.take(i as int)))),
            cons(p0) <= content@.len() ==> cons(tvops(delta.0@.take(i as int))) <= cons(p0),
        decreases delta.0@.len() - i,
    {
        let ghost p = tvops(delta.0@.take(i as int));
        let ghost o = tvop(delta.0@[i as int]);
        let ghost old_ops = editor_ops@;
        proof {
            assert(tvops(delta.0@.take(i + 1)) =~= p.push(o));
            assert(p.push(o).drop_last() =~= p);
            assert(p0 =~= tvops(delta.0@.take(i + 1)) + tvops(delta.0@.skip(i + 1)));
            lemma_add(tvops(delta.0@.take(i + 1)), tvops(delta.0@.skip(i + 1)));
            lemma_push_unfold(blank(0), p, o);
            lemma_ed_unfold(p, o);
        }
        match &delta.0[i] {
            TextOp::Retain(n) => position += *n,
            TextOp::Delete(n) => {
                // src: `start: Position::try_from_offset(position, content)?,` (and `end` likewise)
                let start = match Position::try_from_offset(position, content) { Ok(p) => p, Err(e) => return Err(e) };
                let end = match Position::try_from_offset(position + *n, content) { Ok(p) => p, Err(e) => return Err(e) };
                editor_ops.push(EditorTextOp { range: Range { start, end }, replacement: String::new() });
                position += *n;
            }
            TextOp::Insert(s) => {
                let start = match Position::try_from_offset(position, content) { Ok(p) => p, Err(e) => return Err(e) };
                let end = match Position::try_from_offset(position, content) { Ok(p) => p, Err(e) => return Err(e) };
                editor_ops.push(EditorTextOp { range: Range { start, end }, replacement: s.clone() });
            }
        }
        proof {
            let e2 = ed_of(tvops(delta.0@.take(i + 1)));
            assert(cons(p.push(o)) <= cons(p0)) by {
                assert(p0 =~= p.push(o) + tvops(delta.0@.skip(i + 1)));
            }
            assert(decodes(editor_ops@, content@, e2)) by {
                assert forall|j: int| 0 <= j < editor_ops@.len() implies {
                    &&& (#[trigger] editor_ops@[j]).range.start.ok(content@) && editor_ops@[j].range.start.off(content@) == e2[j].a
                    &&& editor_ops@[j].range.end.ok(content@) && editor_ops@[j].range.end.off(content@) == e2[j].b
                    &&& editor_ops@[j].replacement@ == e2[j].r
                } by {
                    if j < old_ops.len() { assert(editor_ops@[j] == old_ops[j]); }
                }
            }
        }
        i += 1;
    }
    proof { assert(delta.0@.take(i as int) =~= delta.0@); }
    Ok(EditorTextDelta(editor_ops))
}
// corr-end

// corr: crates/teamtype/src/document.rs :: Document::apply_delta_to_doc
// src: document.rs `Document::apply_delta_to_doc`, Automerge half (the `splice_text` loop) and
// the cached-content half (`delta.apply_to(old_text)`, modelled by `fsem`; it errs iff a
// Retain/Delete passes the end, i.e. iff cons > len, and keeps the unread tail).
// Postcondition: when the delta fits the text, the Automerge text after the loop is exactly the
// cached text `fsem(text, delta)`.
#[verifier::spinoff_prover] #[verifier::rlimit(200)]
pub fn apply_delta_to_doc(delta: &TextDelta, text: &str) -> (r: Result<String, Error>)
    requires
        cons(delta.v()) <= MAXL,
        text@.len() <= L, ins(delta.v()) <= L,
    ensures
        cons(delta.v()) <= text@.len() ==> (r matches Ok(s) && s@ == fsem(text@, delta.v())),
{
    let ghost p = delta.v();
    // src: `let text = text.clone();` / `EditorTextDelta::try_from_delta(delta.clone(), &text)?`
    let ed_delta = match try_from_delta(delta.clone_delta(), text) { Ok(d) => d, Err(e) => return Err(e) };
    let mut doc: Vec<char> = chars_of(text);
    let mut offset: isize = 0;
    proof { axiom_str_len(text); }
    let ghost e = ed_of(p);
    let ghost orig = text@;
    let mut j: usize = 0;
    proof {
        assert(e.take(0) =~= Seq::<Trip>::empty());
    }
    // src: `for op in &ed_delta.0`
    while j < ed_delta.0.len()
        invariant
            cons(p) <= MAXL, text@.len() <= L, ins(p) <= L, p == delta.v(), orig == text@, e == ed_of(p),
            decodes(ed_delta.0@, text@, e),
            j <= e.len(), doc@ == run(orig, e.take(j as int)), offset == osum(e.take(j as int)),
            ed_delta.0@.len() == e.len(),
        decreases ed_delta.0@.len() - j,
    {
        let op = &ed_delta.0[j];
        // src: `op.range.as_relative(&text)?`
        let (start, length) = match op.range.as_relative(text) { Ok(x) => x, Err(e) => return Err(e) };
        proof {
            lemma_ed_split(p, j as int);
            let m = choose|m: int| 0 <= m < p.len() && #[trigger] ed_of(p.take(m)) =~= e.take(j as int)
                && ed_of(p.take(m + 1)) =~= e.take(j as int + 1);
            let q = p.take(m);
            let o = p[m];
            assert(p.take(m + 1) =~= q.push(o));
            lemma_cons_prefix(p, m + 1);
            lemma_push_unfold(blank(cons(q.push(o)) as int), q, o);
            lemma_ed_unfold(q, o);
            let t = e[j as int];
            assert(e.take(j as int + 1).last() == t);
            assert(e.take(j as int + 1).drop_last() =~= e.take(j as int));
            assert(ed_of(q.push(o)).last() == t);
            assert(ed_of(q.push(o)).drop_last() =~= ed_of(q));
            assert(ed_delta.0@[j as int].range.start.ok(text@) && ed_delta.0@[j as int].range.end.ok(text@));
            // t.b is an offset of the text, so the op fits
            lemma_off_le(text@, ed_delta.0@[j as int].range.end);
            assert(t.b <= text@.len());
            assert(t.a == cons(q) as int);
            assert(cons(q) + cons_of(o) <= orig.len());
            lemma_run_step(orig, q, o);
            lemma_cons_prefix(q, q.len() as int);
            lemma_run_fsem(orig, q);
            lemma_len(orig.take(cons(q) as int), q);
            assert(start as int == t.a && length as int == t.b - t.a);
            assert(osum(e.take(j as int)) == prod(q) as int - cons(q) as int);
            assert(doc@ == fsem(orig, q));
            assert(doc@.len() == prod(q) + orig.len() - cons(q));
            assert(prod(q) <= cons(q) + ins(q));
            assert(ins(q) <= ins(p));
            assert(ed_delta.0@[j as int].replacement@.len() <= ins(p)) by {
                lemma_cons_prefix(p, m + 1);
                assert(ins(q.push(o)) <= ins(p));
            }
        }
        let rep_len = num_chars(op.replacement.as_str());
        let at = ((start as isize) + offset) as usize;
        // src: `self.doc.splice_text(text_obj, start + offset, length, &op.replacement).expect(..)`
        splice_chars(&mut doc, at, length, op.replacement.as_str());
        offset = offset - (length as isize) + (rep_len as isize);
        proof {
            let t = e[j as int];
            assert(e.take(j as int + 1).drop_last() =~= e.take(j as int));
            assert(e.take(j as int + 1).last() == t);
        }
        j += 1;
    }
    proof {
        if cons(p) <= text@.len() {
            assert(j == ed_delta.0@.len());
            assert(e.take(j as int) =~= e);
            lemma_run_fsem(orig, p);
        }
    }
    Ok(string_of(&doc))
}
// corr-end

fn main() {}
}
