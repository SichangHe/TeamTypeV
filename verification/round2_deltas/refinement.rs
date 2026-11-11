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

// ======================= real code: operational-transform 0.6.1 =======================

pub enum Operation {
    Delete(u64),
    Retain(u64),
    Insert(String),
}

// src: `#[derive(Clone)]` / `.cloned()`
pub fn clone_op(o: &Operation) -> (r: Operation)
    ensures vop(r) == vop(*o),
{
    match o {
        Operation::Delete(n) => Operation::Delete(*n),
        Operation::Retain(n) => Operation::Retain(*n),
        Operation::Insert(s) => Operation::Insert(s.clone()),
    }
}

pub struct OTError;

pub fn is_insert(o: &Operation) -> (r: bool) ensures r == (*o is Insert),
{ match o { Operation::Insert(_) => true, _ => false } }
pub fn is_delete(o: &Operation) -> (r: bool) ensures r == (*o is Delete),
{ match o { Operation::Delete(_) => true, _ => false } }

pub struct OperationSeq {
    pub ops: Vec<Operation>,
    pub base_len: usize,
    pub target_len: usize,
}

// stands for `ops.next()` on `final(self).ops.iter().cloned()`
pub fn next_op(ops: &Vec<Operation>, i: &mut usize) -> (r: Option<Operation>)
    requires *old(i) <= ops.len(),
    ensures
        *old(i) < ops.len() ==> *final(i) == *old(i) + 1 && r is Some && vop(r->Some_0) == vop(ops@[*old(i) as int]),
        *old(i) == ops.len() ==> *final(i) == *old(i) && r is None,
{
    if *i < ops.len() { let o = clone_op(&ops[*i]); *i = *i + 1; Some(o) } else { None }
}

impl OperationSeq {
    pub open spec fn v(&self) -> Seq<SOp> { vops(self.ops@) }

    // representation invariant: cached lengths are exact and bounded
    pub open spec fn wf(&self) -> bool {
        &&& self.base_len == cons(self.v())
        &&& self.target_len == prod(self.v())
        &&& self.base_len <= MAXL
        &&& self.target_len <= MAXL
        &&& forall|i: int| 0 <= i < self.v().len() ==> nz(#[trigger] self.v()[i])
    }

    // src: `#[derive(Default)]`
    pub fn default() -> (r: Self)
        ensures r.wf(), r.ops@.len() == 0, ins(r.v()) == 0,
    {
        let r = OperationSeq { ops: Vec::new(), base_len: 0, target_len: 0 };
        assert(r.v() =~= Seq::<SOp>::empty());
        r
    }

    // corr: verification/vendored_crates/operational-transform-0.6.1/lib.rs :: OperationSeq::delete
    pub fn delete(&mut self, n: u64)
        requires old(self).wf(), old(self).base_len + n <= MAXL,
        ensures
            final(self).wf(), final(self).base_len == old(self).base_len + n, final(self).target_len == old(self).target_len,
            ins(final(self).v()) == ins(old(self).v()),
            forall|t: Seq<char>| t.len() == final(self).base_len ==>
                #[trigger] sem(t, final(self).v()) == sem(t.take(old(self).base_len as int), old(self).v()),
    {
        let ghost o = self.v();
        if n == 0 {
            assert forall|t: Seq<char>| t.len() == self.base_len implies
                #[trigger] sem(t, final(self).v()) == sem(t.take(old(self).base_len as int), old(self).v()) by {
                assert(t.take(t.len() as int) =~= t);
            }
            return;
        }
        self.base_len += n as usize;
        let l = self.ops.len();
        // src: `if let Some(Operation::Delete(n_last)) = self.ops.last_mut() { *n_last += n; }`
        let last = if l > 0 { match &self.ops[l - 1] { Operation::Delete(k) => Some(*k), _ => None } } else { None };
        match last {
            Some(n_last) => {
                let ghost p = o.drop_last();
                proof {
                    lemma_one(blank(n_last as int), SOp::D(n_last as nat));
                    assert(o =~= p + seq![SOp::D(n_last as nat)]);
                    lemma_split(blank((cons(p) + n_last) as int), p, seq![SOp::D(n_last as nat)]);
                }
                assert(n_last <= cons(o));
                self.ops.set(l - 1, Operation::Delete(n_last + n));
                proof {
                    lemma_vops_update(old(self).ops@, l - 1, Operation::Delete((n_last + n) as u64));
                    assert(self.v() =~= p + seq![SOp::D((n_last + n) as nat)]);
                    lemma_one(blank(((n_last + n) as nat) as int), SOp::D((n_last + n) as nat));
                    lemma_split(blank((cons(p) + n_last + n) as int), p, seq![SOp::D((n_last + n) as nat)]);
                    assert forall|t: Seq<char>| t.len() == self.base_len implies
                        #[trigger] sem(t, self.v()) == sem(t.take(old(self).base_len as int), o) by {
                        lemma_split(t, p, seq![SOp::D((n_last + n) as nat)]);
                        lemma_one(t.skip(cons(p) as int), SOp::D((n_last + n) as nat));
                        let t0 = t.take(old(self).base_len as int);
                        lemma_split(t0, p, seq![SOp::D(n_last as nat)]);
                        lemma_one(t0.skip(cons(p) as int), SOp::D(n_last as nat));
                        assert(t0.take(cons(p) as int) =~= t.take(cons(p) as int));
                    }
                }
            }
            None => {
                self.ops.push(Operation::Delete(n));
                proof {
                    lemma_vops_push(old(self).ops@, Operation::Delete(n));
                    let q = seq![SOp::D(n as nat)];
                    assert(self.v() =~= o + q);
                    lemma_one(blank((n as nat) as int), SOp::D(n as nat));
                    lemma_split(blank((cons(o) + n) as int), o, q);
                    assert forall|t: Seq<char>| t.len() == self.base_len implies
                        #[trigger] sem(t, self.v()) == sem(t.take(old(self).base_len as int), o) by {
                        lemma_split(t, o, q);
                        lemma_one(t.skip(cons(o) as int), SOp::D(n as nat));
                        assert(sem(t.take(cons(o) as int), o) + seq![] =~= sem(t.take(cons(o) as int), o));
                    }
                }
            }
        }
    }
    // corr-end

    // corr: verification/vendored_crates/operational-transform-0.6.1/lib.rs :: OperationSeq::retain
    pub fn retain(&mut self, n: u64)
        requires old(self).wf(), old(self).base_len + n <= MAXL, old(self).target_len + n <= MAXL,
        ensures
            final(self).wf(), final(self).base_len == old(self).base_len + n, final(self).target_len == old(self).target_len + n,
            ins(final(self).v()) == ins(old(self).v()),
            forall|t: Seq<char>| t.len() == final(self).base_len ==>
                #[trigger] sem(t, final(self).v()) == sem(t.take(old(self).base_len as int), old(self).v()) + t.skip(old(self).base_len as int),
    {
        let ghost o = self.v();
        if n == 0 {
            assert forall|t: Seq<char>| t.len() == self.base_len implies
                #[trigger] sem(t, final(self).v()) == sem(t.take(old(self).base_len as int), o) + t.skip(old(self).base_len as int) by {
                assert(t.take(t.len() as int) =~= t);
                assert(sem(t, o) + t.skip(t.len() as int) =~= sem(t, o));
            }
            return;
        }
        self.base_len += n as usize;
        self.target_len += n as usize;
        let l = self.ops.len();
        // src: `if let Some(Operation::Retain(i_last)) = self.ops.last_mut() { *i_last += n; }`
        let last = if l > 0 { match &self.ops[l - 1] { Operation::Retain(k) => Some(*k), _ => None } } else { None };
        match last {
            Some(i_last) => {
                let ghost p = o.drop_last();
                proof {
                    assert(o =~= p + seq![SOp::R(i_last as nat)]);
                    lemma_one(blank((i_last as nat) as int), SOp::R(i_last as nat));
                    lemma_split(blank((cons(p) + i_last) as int), p, seq![SOp::R(i_last as nat)]);
                }
                self.ops.set(l - 1, Operation::Retain(i_last + n));
                proof {
                    let q = seq![SOp::R((i_last + n) as nat)];
                    lemma_vops_update(old(self).ops@, l - 1, Operation::Retain((i_last + n) as u64));
                    assert(self.v() =~= p + q);
                    lemma_one(blank(((i_last + n) as nat) as int), SOp::R((i_last + n) as nat));
                    lemma_split(blank((cons(p) + i_last + n) as int), p, q);
                    assert forall|t: Seq<char>| t.len() == self.base_len implies
                        #[trigger] sem(t, self.v()) == sem(t.take(old(self).base_len as int), o) + t.skip(old(self).base_len as int) by {
                        lemma_split(t, p, q);
                        lemma_one(t.skip(cons(p) as int), SOp::R((i_last + n) as nat));
                        let t0 = t.take(old(self).base_len as int);
                        lemma_split(t0, p, seq![SOp::R(i_last as nat)]);
                        lemma_one(t0.skip(cons(p) as int), SOp::R(i_last as nat));
                        assert(t0.take(cons(p) as int) =~= t.take(cons(p) as int));
                        assert(t.skip(cons(p) as int) =~= t0.skip(cons(p) as int) + t.skip(old(self).base_len as int));
                    }
                }
            }
            None => {
                self.ops.push(Operation::Retain(n));
                proof {
                    lemma_vops_push(old(self).ops@, Operation::Retain(n));
                    let q = seq![SOp::R(n as nat)];
                    assert(self.v() =~= o + q);
                    lemma_one(blank((n as nat) as int), SOp::R(n as nat));
                    lemma_split(blank((cons(o) + n) as int), o, q);
                    assert forall|t: Seq<char>| t.len() == self.base_len implies
                        #[trigger] sem(t, self.v()) == sem(t.take(old(self).base_len as int), o) + t.skip(old(self).base_len as int) by {
                        lemma_split(t, o, q);
                        lemma_one(t.skip(cons(o) as int), SOp::R(n as nat));
                    }
                }
            }
        }
    }
    // corr-end

    // corr: verification/vendored_crates/operational-transform-0.6.1/lib.rs :: OperationSeq::insert
    #[verifier::spinoff_prover] #[verifier::rlimit(60)]
    pub fn insert(&mut self, s: &str)
        requires old(self).wf(), old(self).target_len + s@.len() <= MAXL,
        ensures
            final(self).wf(), final(self).base_len == old(self).base_len, final(self).target_len == old(self).target_len + s@.len(),
            ins(final(self).v()) == ins(old(self).v()) + s@.len(),
            forall|t: Seq<char>| t.len() == final(self).base_len ==>
                #[trigger] sem(t, final(self).v()) == sem(t, old(self).v()) + s@,
    {
        let ghost o = self.v();
        // src: `if s.is_empty()`
        if num_chars(s) == 0 {
            assert forall|t: Seq<char>| t.len() == self.base_len implies
                #[trigger] sem(t, final(self).v()) == sem(t, o) + s@ by {
                assert(sem(t, o) + s@ =~= sem(t, o));
            }
            return;
        }
        self.target_len += num_chars(s);
        let l = self.ops.len();
        // src: `match self.ops.as_mut_slice() { [.., Insert(s_last)] => .., [.., Insert(s_pre_last), Delete(_)] => .., [.., op_last @ Delete(_)] => .., _ => .. }`
        let case = if l >= 1 && is_insert(&self.ops[l - 1]) { 1u8 }
            else if l >= 2 && is_insert(&self.ops[l - 2]) && is_delete(&self.ops[l - 1]) { 2u8 }
            else if l >= 1 && is_delete(&self.ops[l - 1]) { 3u8 }
            else { 4u8 };
        if case == 1 {
            // src: `*s_last += s; return;`
            let ghost p = o.drop_last();
            let s_new = match &self.ops[l - 1] { Operation::Insert(s_last) => concat(s_last, s), _ => { proof { assert(false); } unreachable_panic() } };
            let ghost s_last = o.last()->I_0;
            proof { assert(o =~= p + seq![SOp::I(s_last)]); }
            self.ops.set(l - 1, Operation::Insert(s_new));
            proof {
                lemma_vops_update(old(self).ops@, l - 1, Operation::Insert(s_new));
                assert(self.v() =~= p + seq![SOp::I(s_last + s@)]);
                lemma_one(Seq::<char>::empty(), SOp::I(s_last));
                lemma_one(Seq::<char>::empty(), SOp::I(s_last + s@));
                lemma_split(blank((cons(p)) as int), p, seq![SOp::I(s_last)]);
                lemma_split(blank((cons(p)) as int), p, seq![SOp::I(s_last + s@)]);
                assert forall|t: Seq<char>| t.len() == self.base_len implies
                    #[trigger] sem(t, self.v()) == sem(t, o) + s@ by {
                    lemma_split(t, p, seq![SOp::I(s_last)]);
                    lemma_split(t, p, seq![SOp::I(s_last + s@)]);
                    lemma_one(t.skip(cons(p) as int), SOp::I(s_last));
                    lemma_one(t.skip(cons(p) as int), SOp::I(s_last + s@));
                    assert(sem(t.take(cons(p) as int), p) + (s_last + s@) =~= sem(t.take(cons(p) as int), p) + s_last + s@);
                }
            }
            return;
        } else if case == 2 {
            // src: `*s_pre_last += s; return;`
            let ghost p = o.take(l - 2);
            let s_new = match &self.ops[l - 2] { Operation::Insert(s_pre_last) => concat(s_pre_last, s), _ => { proof { assert(false); } unreachable_panic() } };
            let ghost s_pre = o[l - 2]->I_0;
            let ghost k = o[l - 1]->D_0;
            let ghost q0 = seq![SOp::I(s_pre), SOp::D(k)];
            let ghost q1 = seq![SOp::I(s_pre + s@), SOp::D(k)];
            proof { assert(o =~= p + q0); }
            self.ops.set(l - 2, Operation::Insert(s_new));
            proof {
                lemma_vops_update(old(self).ops@, l - 2, Operation::Insert(s_new));
                assert(self.v() =~= p + q1);
                let w = blank((k) as int);
                lemma_id(s_pre, k, w);
                lemma_id(s_pre + s@, k, w);
                lemma_split(blank((cons(p) + k) as int), p, q0);
                lemma_split(blank((cons(p) + k) as int), p, q1);
                assert forall|t: Seq<char>| t.len() == self.base_len implies
                    #[trigger] sem(t, self.v()) == sem(t, o) + s@ by {
                    lemma_split(t, p, q0);
                    lemma_split(t, p, q1);
                    lemma_id(s_pre, k, t.skip(cons(p) as int));
                    lemma_id(s_pre + s@, k, t.skip(cons(p) as int));
                    assert(sem(t.take(cons(p) as int), p) + (s_pre + s@) =~= sem(t.take(cons(p) as int), p) + s_pre + s@);
                }
            }
            return;
        } else if case == 3 {
            // src: `let new_last = op_last.clone(); *op_last = Operation::Insert(s.to_owned()); new_last` then push
            let ghost p = o.drop_last();
            let new_last = clone_op(&self.ops[l - 1]);
            let ghost k = o.last()->D_0;
            self.ops.set(l - 1, Operation::Insert(to_owned(s)));
            self.ops.push(new_last);
            proof {
                let q0 = seq![SOp::D(k)];
                let q1 = seq![SOp::I(s@), SOp::D(k)];
                assert(o =~= p + q0);
                lemma_vops_update(old(self).ops@, l - 1, Operation::Insert(self.ops@[l - 1]->Insert_0));
                lemma_vops_push(old(self).ops@.update(l - 1, self.ops@[l - 1]), new_last);
                assert(self.v() =~= p + q1);
                let w = blank((k) as int);
                lemma_id(s@, k, w);
                lemma_one(w, SOp::D(k));
                lemma_split(blank((cons(p) + k) as int), p, q0);
                lemma_split(blank((cons(p) + k) as int), p, q1);
                assert forall|t: Seq<char>| t.len() == self.base_len implies
                    #[trigger] sem(t, self.v()) == sem(t, o) + s@ by {
                    lemma_split(t, p, q0);
                    lemma_split(t, p, q1);
                    lemma_id(s@, k, t.skip(cons(p) as int));
                    lemma_one(t.skip(cons(p) as int), SOp::D(k));
                    assert(sem(t.take(cons(p) as int), p) + seq![] =~= sem(t.take(cons(p) as int), p));
                }
            }
        } else {
            // src: `_ => Operation::Insert(s.to_owned())` then push
            self.ops.push(Operation::Insert(to_owned(s)));
            proof {
                let q = seq![SOp::I(s@)];
                lemma_vops_push(old(self).ops@, self.ops@.last());
                assert(self.v() =~= o + q);
                lemma_one(Seq::<char>::empty(), SOp::I(s@));
                lemma_split(blank((cons(o)) as int), o, q);
                assert forall|t: Seq<char>| t.len() == self.base_len implies
                    #[trigger] sem(t, self.v()) == sem(t, o) + s@ by {
                    lemma_split(t, o, q);
                    lemma_one(t.skip(cons(o) as int), SOp::I(s@));
                    assert(t.take(cons(o) as int) =~= t);
                }
            }
        }
    }
    // corr-end
    // src: `pub fn transform(&self, other: &Self) -> Result<(Self, Self), OTError>`
    // The only signature change is the erased ghost argument `doc`: any text the
    // inputs apply to. Callers may pass any such text, so the ensures holds for all.
    // corr: verification/vendored_crates/operational-transform-0.6.1/lib.rs :: OperationSeq::transform
    #[verifier::spinoff_prover] #[verifier::rlimit(4000)]
    pub fn transform(&self, other: &Self, Ghost(doc): Ghost<Seq<char>>) -> (r: Result<(Self, Self), OTError>)
        requires
            self.wf(), other.wf(), self.target_len + other.target_len <= MAXL,
            doc.len() == self.base_len,
        ensures
            self.base_len != other.base_len ==> r is Err,
            self.base_len == other.base_len ==> r is Ok && ({
                let (a_prime, b_prime) = r->Ok_0;
                &&& a_prime.wf() && b_prime.wf()
                &&& a_prime.base_len == other.target_len
                &&& b_prime.base_len == self.target_len
                &&& a_prime.target_len == b_prime.target_len
                &&& a_prime.target_len <= self.target_len + other.target_len
                &&& ins(a_prime.v()) == ins(self.v())
                &&& ins(b_prime.v()) == ins(other.v())
                // convergence of the real transform
                &&& sem(sem(doc, self.v()), b_prime.v()) == sem(sem(doc, other.v()), a_prime.v())
            }),
    {
        if self.base_len != other.base_len {
            return Err(OTError);
        }

        let mut a_prime = OperationSeq::default();
        let mut b_prime = OperationSeq::default();

        // src: `let mut ops1 = self.ops.iter().cloned();` (and ops2)
        let mut i1: usize = 0;
        let mut i2: usize = 0;

        let mut maybe_op1 = next_op(&self.ops, &mut i1);
        let mut maybe_op2 = next_op(&other.ops, &mut i2);
        let ghost n = self.base_len as nat;
        let ghost mut k: nat = 0;
        let ghost mut ta: Seq<char> = seq![];
        let ghost mut tb: Seq<char> = seq![];
        proof {
            lemma_next(self.ops@, 0, maybe_op1, i1);
            lemma_next(other.ops@, 0, maybe_op2, i2);
            lemma_vops_skip0(self.ops@);
            lemma_vops_skip0(other.ops@);
            assert(doc.skip(0) =~= doc);
            assert(seq![] + sem(doc, self.v()) =~= sem(doc, self.v()));
            assert(seq![] + sem(doc, other.v()) =~= sem(doc, other.v()));
            assert(a_prime.v() =~= Seq::<SOp>::empty());
            assert(b_prime.v() =~= Seq::<SOp>::empty());
            if maybe_op1 is Some { assert(vop(maybe_op1->Some_0) == self.v()[0]); }
            if maybe_op2 is Some { assert(vop(maybe_op2->Some_0) == other.v()[0]); }
        }
        loop
            invariant
                self.wf(), other.wf(), self.target_len + other.target_len <= MAXL,
                doc.len() == n, n == self.base_len, n == other.base_len,
                i1 <= self.ops.len(), i2 <= other.ops.len(),
                maybe_op1 is None ==> i1 == self.ops.len(),
                maybe_op2 is None ==> i2 == other.ops.len(),
                maybe_op1 is Some ==> nz(vop(maybe_op1->Some_0)),
                maybe_op2 is Some ==> nz(vop(maybe_op2->Some_0)),
                k <= n,
                k + cons(rem(self.ops@, maybe_op1, i1)) == n,
                k + cons(rem(other.ops@, maybe_op2, i2)) == n,
                sem(doc, self.v()) == ta + sem(doc.skip(k as int), rem(self.ops@, maybe_op1, i1)),
                sem(doc, other.v()) == tb + sem(doc.skip(k as int), rem(other.ops@, maybe_op2, i2)),
                self.target_len == ta.len() + prod(rem(self.ops@, maybe_op1, i1)),
                other.target_len == tb.len() + prod(rem(other.ops@, maybe_op2, i2)),
                ins(self.v()) == ins(a_prime.v()) + ins(rem(self.ops@, maybe_op1, i1)),
                ins(other.v()) == ins(b_prime.v()) + ins(rem(other.ops@, maybe_op2, i2)),
                a_prime.wf(), b_prime.wf(),
                a_prime.base_len == tb.len(), b_prime.base_len == ta.len(),
                a_prime.target_len == b_prime.target_len,
                a_prime.target_len <= ta.len() + tb.len(),
                sem(tb, a_prime.v()) == sem(ta, b_prime.v()),
            ensures
                maybe_op1 is None, maybe_op2 is None,
                a_prime.wf(), b_prime.wf(),
                a_prime.base_len == tb.len(), b_prime.base_len == ta.len(),
                a_prime.target_len == b_prime.target_len,
                a_prime.target_len <= ta.len() + tb.len(),
                sem(tb, a_prime.v()) == sem(ta, b_prime.v()),
                sem(doc, self.v()) == ta, sem(doc, other.v()) == tb,
                self.target_len == ta.len(), other.target_len == tb.len(),
                ins(self.v()) == ins(a_prime.v()), ins(other.v()) == ins(b_prime.v()),
            decreases
                (if maybe_op1 is Some { 1int } else { 0int }) + self.ops.len() - i1
                + (if maybe_op2 is Some { 1int } else { 0int }) + other.ops.len() - i2,
        {
            let ghost mo1 = maybe_op1;
            let ghost mo2 = maybe_op2;
            let ghost j1 = i1;
            let ghost j2 = i2;
            let ghost ap = a_prime;
            let ghost bp = b_prime;
            let ghost t = doc.skip(k as int);
            proof {
                if mo1 is None { assert(rem(self.ops@, mo1, j1) =~= Seq::<SOp>::empty()); }
                if mo2 is None { assert(rem(other.ops@, mo2, j2) =~= Seq::<SOp>::empty()); }
                if mo1 is Some { lemma_rem_some(self.ops@, mo1->Some_0, j1); lemma_add(seq![vop(mo1->Some_0)], vops(self.ops@.skip(j1 as int))); lemma_one(blank(cons_of(vop(mo1->Some_0)) as int), vop(mo1->Some_0)); }
                if mo2 is Some { lemma_rem_some(other.ops@, mo2->Some_0, j2); lemma_add(seq![vop(mo2->Some_0)], vops(other.ops@.skip(j2 as int))); lemma_one(blank(cons_of(vop(mo2->Some_0)) as int), vop(mo2->Some_0)); }
                lemma_len(t, rem(self.ops@, mo1, j1));
                lemma_len(t, rem(other.ops@, mo2, j2));
            }
            match (&maybe_op1, &maybe_op2) {
                (None, None) => {
                    proof {
                        assert(t =~= seq![]);
                        assert(ta + seq![] =~= ta);
                        assert(tb + seq![] =~= tb);
                    }
                    break
                }
                (Some(Operation::Insert(s)), _) => {
                    a_prime.insert(s.as_str());
                    b_prime.retain(num_chars(s.as_str()) as u64); // src: `num_chars(s.as_bytes()) as _`
                    maybe_op1 = next_op(&self.ops, &mut i1);
                    proof {
                        let o = mo1->Some_0;
                        let x = o->Insert_0@;
                        lemma_adv_whole(self.ops@, o, j1, maybe_op1, i1, t);
                        if maybe_op1 is Some { assert(vop(maybe_op1->Some_0) == self.v()[j1 as int]); }
                        assert(t.take(0) =~= seq![]);
                        assert(t.skip(0) =~= t);
                        assert(sem(tb, a_prime.v()) == sem(tb, ap.v()) + x);
                        let tt = ta + x;
                        assert(tt.take(ta.len() as int) =~= ta);
                        assert(tt.skip(ta.len() as int) =~= x);
                        assert(sem(tt, b_prime.v()) == sem(ta, bp.v()) + x);
                        assert(sem(doc, self.v()) =~= tt + sem(t, rem(self.ops@, maybe_op1, i1)));
                        ta = tt;
                    }
                }
                (_, Some(Operation::Insert(s))) => {
                    a_prime.retain(num_chars(s.as_str()) as u64); // src: `num_chars(s.as_bytes()) as _`
                    b_prime.insert(s.as_str());
                    maybe_op2 = next_op(&other.ops, &mut i2);
                    proof {
                        let o = mo2->Some_0;
                        let x = o->Insert_0@;
                        lemma_adv_whole(other.ops@, o, j2, maybe_op2, i2, t);
                        if maybe_op2 is Some { assert(vop(maybe_op2->Some_0) == other.v()[j2 as int]); }
                        assert(t.take(0) =~= seq![]);
                        assert(t.skip(0) =~= t);
                        assert(sem(ta, b_prime.v()) == sem(ta, bp.v()) + x);
                        let tt = tb + x;
                        assert(tt.take(tb.len() as int) =~= tb);
                        assert(tt.skip(tb.len() as int) =~= x);
                        assert(sem(tt, a_prime.v()) == sem(tb, ap.v()) + x);
                        assert(sem(doc, other.v()) =~= tt + sem(t, rem(other.ops@, maybe_op2, i2)));
                        tb = tt;
                    }
                }
                (None, _) => {
                    proof { assert(false); }
                    return Err(OTError);
                }
                (_, None) => {
                    proof { assert(false); }
                    return Err(OTError);
                }
                (Some(Operation::Retain(i)), Some(Operation::Retain(j))) => {
                    let i = *i;
                    let j = *j;
                    let ghost m: nat = if i < j { i as nat } else { j as nat };
                    let ghost w = t.take(m as int);
                    // src: `match i.cmp(j) { Ordering::Less => .., Ordering::Equal => .., Ordering::Greater => .. }`
                    if i < j {
                        a_prime.retain(i);
                        b_prime.retain(i);
                        maybe_op2 = Some(Operation::Retain(j - i));
                        maybe_op1 = next_op(&self.ops, &mut i1);
                    } else if i == j {
                        a_prime.retain(i);
                        b_prime.retain(i);
                        maybe_op1 = next_op(&self.ops, &mut i1);
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    } else {
                        a_prime.retain(j);
                        b_prime.retain(j);
                        maybe_op1 = Some(Operation::Retain(i - j));
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    }
                    proof {
                        if i <= j { lemma_adv_whole(self.ops@, mo1->Some_0, j1, maybe_op1, i1, t); }
                        else { lemma_adv_part(self.ops@, mo1->Some_0, j1, maybe_op1->Some_0, m, t); }
                        if j <= i { lemma_adv_whole(other.ops@, mo2->Some_0, j2, maybe_op2, i2, t); }
                        else { lemma_adv_part(other.ops@, mo2->Some_0, j2, maybe_op2->Some_0, m, t); }
                        if i <= j && maybe_op1 is Some { assert(vop(maybe_op1->Some_0) == self.v()[j1 as int]); }
                        if j <= i && maybe_op2 is Some { assert(vop(maybe_op2->Some_0) == other.v()[j2 as int]); }
                        let ua = ta + w;
                        let ub = tb + w;
                        assert(ua.take(ta.len() as int) =~= ta);
                        assert(ua.skip(ta.len() as int) =~= w);
                        assert(ub.take(tb.len() as int) =~= tb);
                        assert(ub.skip(tb.len() as int) =~= w);
                        assert(sem(ub, a_prime.v()) == sem(tb, ap.v()) + w);
                        assert(sem(ua, b_prime.v()) == sem(ta, bp.v()) + w);
                        assert(t.skip(m as int) =~= doc.skip((k + m) as int));
                        assert(sem(doc, self.v()) =~= ua + sem(doc.skip((k + m) as int), rem(self.ops@, maybe_op1, i1)));
                        assert(sem(doc, other.v()) =~= ub + sem(doc.skip((k + m) as int), rem(other.ops@, maybe_op2, i2)));
                        ta = ua;
                        tb = ub;
                        k = k + m;
                    }
                }
                (Some(Operation::Delete(i)), Some(Operation::Delete(j))) => {
                    let i = *i;
                    let j = *j;
                    let ghost m: nat = if i < j { i as nat } else { j as nat };
                    // src: `match i.cmp(j)`
                    if i < j {
                        maybe_op2 = Some(Operation::Delete(j - i));
                        maybe_op1 = next_op(&self.ops, &mut i1);
                    } else if i == j {
                        maybe_op1 = next_op(&self.ops, &mut i1);
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    } else {
                        maybe_op1 = Some(Operation::Delete(i - j));
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    }
                    proof {
                        if i <= j { lemma_adv_whole(self.ops@, mo1->Some_0, j1, maybe_op1, i1, t); }
                        else { lemma_adv_part(self.ops@, mo1->Some_0, j1, maybe_op1->Some_0, m, t); }
                        if j <= i { lemma_adv_whole(other.ops@, mo2->Some_0, j2, maybe_op2, i2, t); }
                        else { lemma_adv_part(other.ops@, mo2->Some_0, j2, maybe_op2->Some_0, m, t); }
                        if i <= j && maybe_op1 is Some { assert(vop(maybe_op1->Some_0) == self.v()[j1 as int]); }
                        if j <= i && maybe_op2 is Some { assert(vop(maybe_op2->Some_0) == other.v()[j2 as int]); }
                        assert(t.skip(m as int) =~= doc.skip((k + m) as int));
                        assert(ta + seq![] =~= ta);
                        assert(tb + seq![] =~= tb);
                        assert(sem(doc, self.v()) =~= ta + sem(doc.skip((k + m) as int), rem(self.ops@, maybe_op1, i1)));
                        assert(sem(doc, other.v()) =~= tb + sem(doc.skip((k + m) as int), rem(other.ops@, maybe_op2, i2)));
                        k = k + m;
                    }
                }
                (Some(Operation::Delete(i)), Some(Operation::Retain(j))) => {
                    let i = *i;
                    let j = *j;
                    let ghost m: nat = if i < j { i as nat } else { j as nat };
                    let ghost w = t.take(m as int);
                    // src: `match i.cmp(j)`
                    if i < j {
                        a_prime.delete(i);
                        maybe_op2 = Some(Operation::Retain(j - i));
                        maybe_op1 = next_op(&self.ops, &mut i1);
                    } else if i == j {
                        a_prime.delete(i);
                        maybe_op1 = next_op(&self.ops, &mut i1);
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    } else {
                        a_prime.delete(j);
                        maybe_op1 = Some(Operation::Delete(i - j));
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    }
                    proof {
                        if i <= j { lemma_adv_whole(self.ops@, mo1->Some_0, j1, maybe_op1, i1, t); }
                        else { lemma_adv_part(self.ops@, mo1->Some_0, j1, maybe_op1->Some_0, m, t); }
                        if j <= i { lemma_adv_whole(other.ops@, mo2->Some_0, j2, maybe_op2, i2, t); }
                        else { lemma_adv_part(other.ops@, mo2->Some_0, j2, maybe_op2->Some_0, m, t); }
                        if i <= j && maybe_op1 is Some { assert(vop(maybe_op1->Some_0) == self.v()[j1 as int]); }
                        if j <= i && maybe_op2 is Some { assert(vop(maybe_op2->Some_0) == other.v()[j2 as int]); }
                        let ub = tb + w;
                        assert(ub.take(tb.len() as int) =~= tb);
                        assert(sem(ub, a_prime.v()) == sem(tb, ap.v()));
                        assert(t.skip(m as int) =~= doc.skip((k + m) as int));
                        assert(ta + seq![] =~= ta);
                        assert(sem(doc, self.v()) =~= ta + sem(doc.skip((k + m) as int), rem(self.ops@, maybe_op1, i1)));
                        assert(sem(doc, other.v()) =~= ub + sem(doc.skip((k + m) as int), rem(other.ops@, maybe_op2, i2)));
                        tb = ub;
                        k = k + m;
                    }
                }
                (Some(Operation::Retain(i)), Some(Operation::Delete(j))) => {
                    let i = *i;
                    let j = *j;
                    let ghost m: nat = if i < j { i as nat } else { j as nat };
                    let ghost w = t.take(m as int);
                    // src: `match i.cmp(j)`
                    if i < j {
                        b_prime.delete(i);
                        maybe_op2 = Some(Operation::Delete(j - i));
                        maybe_op1 = next_op(&self.ops, &mut i1);
                    } else if i == j {
                        b_prime.delete(i);
                        maybe_op1 = next_op(&self.ops, &mut i1);
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    } else {
                        b_prime.delete(j);
                        maybe_op1 = Some(Operation::Retain(i - j));
                        maybe_op2 = next_op(&other.ops, &mut i2);
                    }
                    proof {
                        if i <= j { lemma_adv_whole(self.ops@, mo1->Some_0, j1, maybe_op1, i1, t); }
                        else { lemma_adv_part(self.ops@, mo1->Some_0, j1, maybe_op1->Some_0, m, t); }
                        if j <= i { lemma_adv_whole(other.ops@, mo2->Some_0, j2, maybe_op2, i2, t); }
                        else { lemma_adv_part(other.ops@, mo2->Some_0, j2, maybe_op2->Some_0, m, t); }
                        if i <= j && maybe_op1 is Some { assert(vop(maybe_op1->Some_0) == self.v()[j1 as int]); }
                        if j <= i && maybe_op2 is Some { assert(vop(maybe_op2->Some_0) == other.v()[j2 as int]); }
                        let ua = ta + w;
                        assert(ua.take(ta.len() as int) =~= ta);
                        assert(sem(ua, b_prime.v()) == sem(ta, bp.v()));
                        assert(t.skip(m as int) =~= doc.skip((k + m) as int));
                        assert(tb + seq![] =~= tb);
                        assert(sem(doc, self.v()) =~= ua + sem(doc.skip((k + m) as int), rem(self.ops@, maybe_op1, i1)));
                        assert(sem(doc, other.v()) =~= tb + sem(doc.skip((k + m) as int), rem(other.ops@, maybe_op2, i2)));
                        ta = ua;
                        k = k + m;
                    }
                }
            }
        }

        Ok((a_prime, b_prime))
    }
    // corr-end
    // src: `pub fn apply(&self, s: &str) -> Result<String, OTError>`
    // corr: verification/vendored_crates/operational-transform-0.6.1/lib.rs :: OperationSeq::apply
    #[verifier::spinoff_prover] #[verifier::rlimit(200)]
    pub fn apply(&self, s: &str) -> (r: Result<String, OTError>)
        requires self.wf(),
        ensures
            s@.len() != self.base_len ==> r is Err,
            s@.len() == self.base_len ==> r is Ok && r->Ok_0@ == sem(s@, self.v()),
    {
        if num_chars(s) != self.base_len {
            return Err(OTError);
        }
        let mut new_s = String::new();
        // src: `let chars = &mut s.chars();` -- the iterator position is `pos`
        let chars = chars_of(s);
        let mut pos: usize = 0;
        // src: `for op in &self.ops`
        let mut idx: usize = 0;
        proof { assert(vops(self.ops@.take(0)) =~= Seq::<SOp>::empty()); }
        while idx < self.ops.len()
            invariant
                self.wf(), chars@ == s@, s@.len() == self.base_len,
                idx <= self.ops.len(),
                pos == cons(vops(self.ops@.take(idx as int))),
                pos <= chars@.len(),
                new_s@ == sem(chars@.take(pos as int), vops(self.ops@.take(idx as int))),
            decreases self.ops.len() - idx,
        {
            let ghost p = vops(self.ops@.take(idx as int));
            let ghost o = vop(self.ops@[idx as int]);
            let ghost pos0 = pos;
            let ghost ns0 = new_s@;
            proof {
                assert(vops(self.ops@.take(idx + 1)) =~= p.push(o));
                assert(self.v() =~= vops(self.ops@.take(idx + 1)) + vops(self.ops@.skip(idx + 1)));
                lemma_add(vops(self.ops@.take(idx + 1)), vops(self.ops@.skip(idx + 1)));
                assert(p.push(o).drop_last() =~= p);
            }
            match &self.ops[idx] {
                Operation::Retain(retain) => {
                    // src: `for c in chars.take(*retain as usize) { new_s.push(c); }`
                    let mut j: u64 = 0;
                    while j < *retain && pos < chars.len()
                        invariant
                            chars@ == s@, j <= *retain, pos == pos0 + j, pos0 + *retain <= chars@.len(),
                            new_s@ == ns0 + chars@.subrange(pos0 as int, pos as int),
                        decreases *retain - j,
                    {
                        push_char(&mut new_s, chars[pos]);
                        pos += 1;
                        j += 1;
                        proof { assert(chars@.subrange(pos0 as int, pos as int) =~= chars@.subrange(pos0 as int, pos - 1).push(chars@[pos - 1])); }
                    }
                    proof {
                        let t = chars@.take(pos as int);
                        assert(t.take(pos0 as int) =~= chars@.take(pos0 as int));
                        assert(t.skip(pos0 as int) =~= chars@.subrange(pos0 as int, pos as int));
                    }
                }
                Operation::Delete(delete) => {
                    // src: `for _ in 0..*delete { chars.next(); }`
                    let mut j: u64 = 0;
                    while j < *delete
                        invariant j <= *delete, pos == pos0 + j, pos0 + *delete <= chars@.len(),
                        decreases *delete - j,
                    {
                        if pos < chars.len() { pos += 1; }
                        j += 1;
                    }
                    proof {
                        let t = chars@.take(pos as int);
                        assert(t.take(pos0 as int) =~= chars@.take(pos0 as int));
                        assert(ns0 + seq![] =~= ns0);
                    }
                }
                Operation::Insert(insert) => {
                    new_s = concat(&new_s, insert.as_str()); // src: `new_s += insert;`
                    proof {
                        let t = chars@.take(pos as int);
                        assert(t.take(pos0 as int) =~= t);
                    }
                }
            }
            idx += 1;
        }
        proof {
            assert(self.ops@.take(idx as int) =~= self.ops@);
            assert(chars@.take(pos as int) =~= s@);
        }
        Ok(new_s)
    }
    // corr-end

    // src: `#[derive(Clone)]`
    pub fn clone_seq(&self) -> (r: Self)
        ensures r.v() == self.v(), r.base_len == self.base_len, r.target_len == self.target_len,
    {
        let mut ops: Vec<Operation> = Vec::new();
        let mut i: usize = 0;
        while i < self.ops.len()
            invariant i <= self.ops.len(), vops(ops@) == vops(self.ops@.take(i as int)),
            decreases self.ops.len() - i,
        {
            let o = clone_op(&self.ops[i]);
            proof { lemma_vops_push(ops@, o); assert(vops(self.ops@.take(i + 1)) =~= vops(self.ops@.take(i as int)).push(vop(self.ops@[i as int]))); }
            ops.push(o);
            i += 1;
        }
        proof { assert(self.ops@.take(i as int) =~= self.ops@); }
        OperationSeq { ops, base_len: self.base_len, target_len: self.target_len }
    }
}

// ======================= real code: teamtype source/ot.rs =======================

// force_apply semantics: apply to the first cons(p) characters, keep the rest
pub open spec fn fsem(t: Seq<char>, p: Seq<SOp>) -> Seq<char> {
    sem(t.take(cons(p) as int), p) + t.skip(cons(p) as int)
}

pub proof fn lemma_fsem_len(t: Seq<char>, p: Seq<SOp>)
    requires cons(p) <= t.len(),
    ensures fsem(t, p).len() == prod(p) + t.len() - cons(p), prod(p) <= cons(p) + ins(p),
{ lemma_len(t.take(cons(p) as int), p); }

pub proof fn lemma_fsem_app(x: Seq<char>, y: Seq<char>, p: Seq<SOp>)
    requires cons(p) == x.len(),
    ensures fsem(x + y, p) == sem(x, p) + y,
{
    assert((x + y).take(x.len() as int) =~= x);
    assert((x + y).skip(x.len() as int) =~= y);
}

// src: `OTServer::force_apply(document: &str, mut op_seq: OperationSeq) -> String`
// (an associated fn without `self`; here a free fn)
// corr: crates/teamtype/src/ot.rs :: OTServer::force_apply
#[verifier::spinoff_prover]
pub fn force_apply(document: &str, op_seq: OperationSeq) -> (r: String)
    requires
        op_seq.wf(), op_seq.base_len <= document@.len(), document@.len() <= MAXL,
        op_seq.target_len + document@.len() - op_seq.base_len <= MAXL,
    ensures r@ == fsem(document@, op_seq.v()),
{
    let mut op_seq = op_seq;
    let ghost old_op = op_seq;
    let doc_chars = num_chars(document); // src: `document.chars().count()`
    if op_seq.base_len < doc_chars {
        op_seq.retain((doc_chars - op_seq.base_len) as u64);
    }
    proof {
        let d = document@;
        if old_op.base_len < d.len() {
            assert(sem(d, op_seq.v()) == sem(d.take(old_op.base_len as int), old_op.v()) + d.skip(old_op.base_len as int));
        } else {
            assert(d.take(d.len() as int) =~= d);
            assert(sem(d, old_op.v()) + d.skip(d.len() as int) =~= sem(d, old_op.v()));
        }
    }
    // src: `op_seq.apply(document).unwrap_or_else(|_| panic!(..))`
    match op_seq.apply(document) {
        Ok(r) => r,
        Err(_) => unreachable_panic(),
    }
}
// corr-end

// result of force-applying `ops` one after another to `u`
pub open spec fn chain(u: Seq<char>, ops: Seq<OperationSeq>) -> Seq<char> decreases ops.len()
{ if ops.len() == 0 { u } else { fsem(chain(u, ops.drop_last()), ops.last().v()) } }

// every op in the chain is well formed and fits the text it is applied to
pub open spec fn chain_ok(u: Seq<char>, ops: Seq<OperationSeq>) -> bool {
    forall|i: int| #![trigger ops[i]] 0 <= i < ops.len() ==> ops[i].wf() && ops[i].base_len <= chain(u, ops.take(i)).len()
}

// src: `fn transform_through_operations(mut their_op_seq: OperationSeq, my_operations: &[OperationSeq]) -> (OperationSeq, Vec<OperationSeq>)`
// Ghost `docs`: docs[0] is the text both sides started from, docs[i+1] is
// docs[i] after my_operations[i].
// corr: crates/teamtype/src/ot.rs :: transform_through_operations
#[verifier::spinoff_prover] #[verifier::rlimit(400)]
pub fn transform_through_operations(
    their_op_seq: OperationSeq,
    my_operations: &[OperationSeq],
    Ghost(docs): Ghost<Seq<Seq<char>>>,
) -> (r: (OperationSeq, Vec<OperationSeq>))
    requires
        their_op_seq.wf(), ins(their_op_seq.v()) <= L,
        docs.len() == my_operations@.len() + 1,
        their_op_seq.base_len <= docs[0].len(),
        forall|i: int| 0 <= i < docs.len() ==> (#[trigger] docs[i]).len() <= L,
        forall|i: int| 0 <= i < my_operations@.len() ==> {
            &&& (#[trigger] my_operations@[i]).wf()
            &&& my_operations@[i].base_len <= docs[i].len()
            &&& docs[i + 1] == fsem(docs[i], my_operations@[i].v())
        },
    ensures ({
        let (their_prime, mine_prime) = r;
        let u0 = fsem(docs[0], their_op_seq.v());
        &&& mine_prime@.len() == my_operations@.len()
        &&& their_prime.wf()
        &&& their_prime.base_len <= docs.last().len()
        &&& chain_ok(u0, mine_prime@)
        // convergence of the queue: their op then my transformed ops equals
        // my ops then their transformed op
        &&& chain(u0, mine_prime@) == fsem(docs.last(), their_prime.v())
    }),
{
    let mut their_op_seq = their_op_seq;
    let ghost their0 = their_op_seq;
    let ghost u0 = fsem(docs[0], their0.v());
    let mut transformed_my_operations: Vec<OperationSeq> = Vec::new();
    // src: `for my_op_seq in my_operations`
    let mut idx: usize = 0;
    proof { assert(transformed_my_operations@.take(0) =~= transformed_my_operations@); }
    while idx < my_operations.len()
        invariant
            idx <= my_operations@.len(),
            docs.len() == my_operations@.len() + 1,
            forall|i: int| 0 <= i < docs.len() ==> (#[trigger] docs[i]).len() <= L,
            forall|i: int| 0 <= i < my_operations@.len() ==> {
                &&& (#[trigger] my_operations@[i]).wf()
                &&& my_operations@[i].base_len <= docs[i].len()
                &&& docs[i + 1] == fsem(docs[i], my_operations@[i].v())
            },
            their_op_seq.wf(), ins(their_op_seq.v()) == ins(their0.v()), ins(their0.v()) <= L,
            their_op_seq.base_len <= docs[idx as int].len(),
            transformed_my_operations@.len() == idx,
            chain_ok(u0, transformed_my_operations@),
            chain(u0, transformed_my_operations@) == fsem(docs[idx as int], their_op_seq.v()),
            u0 == fsem(docs[0], their0.v()),
        decreases my_operations@.len() - idx,
    {
        let ghost d = docs[idx as int];
        let ghost their_old = their_op_seq;
        let mut my_op_seq = my_operations[idx].clone_seq(); // src: `my_op_seq.clone()`
        let ghost my_old = my_op_seq;
        proof {
            lemma_fsem_len(d, my_old.v());
            lemma_fsem_len(d, their_old.v());
            assert(docs[idx + 1].len() <= L);
        }
        if my_op_seq.base_len < their_op_seq.base_len {
            let diff = their_op_seq.base_len - my_op_seq.base_len;
            my_op_seq.retain(diff as u64);
        } else {
            let diff = my_op_seq.base_len - their_op_seq.base_len;
            their_op_seq.retain(diff as u64);
        }
        let ghost pl = my_op_seq.base_len;
        let ghost dp = d.take(pl as int);
        proof {
            // padding does not change force_apply's result
            assert(dp.take(my_old.base_len as int) =~= d.take(my_old.base_len as int));
            assert(dp.skip(my_old.base_len as int) + d.skip(pl as int) =~= d.skip(my_old.base_len as int));
            assert(dp.take(their_old.base_len as int) =~= d.take(their_old.base_len as int));
            assert(dp.skip(their_old.base_len as int) + d.skip(pl as int) =~= d.skip(their_old.base_len as int));
            assert(sem(dp, my_op_seq.v()) == sem(dp.take(my_old.base_len as int), my_old.v()) + dp.skip(my_old.base_len as int));
            assert(sem(dp, their_op_seq.v()) == sem(dp.take(their_old.base_len as int), their_old.v()) + dp.skip(their_old.base_len as int));
            assert(fsem(d, my_op_seq.v()) == fsem(d, my_old.v()));
            assert(fsem(d, their_op_seq.v()) == fsem(d, their_old.v()));
            lemma_fsem_len(d, my_op_seq.v());
            lemma_fsem_len(d, their_op_seq.v());
        }
        // src: `my_op_seq.transform(&their_op_seq).unwrap_or_else(|_| panic!(..))`
        let (my_prime, their_prime) = match my_op_seq.transform(&their_op_seq, Ghost(dp)) {
            Ok(p) => p,
            Err(_) => unreachable_panic(),
        };
        proof {
            let x = sem(dp, my_op_seq.v());
            let y = sem(dp, their_op_seq.v());
            lemma_len(dp, my_op_seq.v());
            lemma_len(dp, their_op_seq.v());
            lemma_fsem_app(x, d.skip(pl as int), their_prime.v());
            lemma_fsem_app(y, d.skip(pl as int), my_prime.v());
            assert(fsem(d, my_op_seq.v()) == x + d.skip(pl as int));
            assert(fsem(d, their_op_seq.v()) == y + d.skip(pl as int));
            let old_t = transformed_my_operations@;
            let new_t = old_t.push(my_prime);
            assert(new_t.drop_last() =~= old_t);
            assert(new_t.take(idx as int) =~= old_t);
            assert forall|i: int| 0 <= i < new_t.len() implies #[trigger] new_t[i].wf() && new_t[i].base_len <= chain(u0, new_t.take(i)).len() by {
                if i < idx { assert(new_t.take(i) =~= old_t.take(i)); }
            }
            lemma_fsem_len(fsem(d, their_op_seq.v()), my_prime.v());
        }
        transformed_my_operations.push(my_prime);
        their_op_seq = their_prime;
        idx += 1;
    }
    (their_op_seq, transformed_my_operations)
}
// corr-end

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

    // corr: crates/teamtype/src/types.rs :: TextDelta::retain
    pub fn retain(&mut self, n: usize)
        ensures final(self).v() == (if n != 0 { old(self).v().push(SOp::R(n as nat)) } else { old(self).v() }),
    {
        if n != 0 {
            self.0.push(TextOp::Retain(n));
            proof { assert(self.v() =~= old(self).v().push(SOp::R(n as nat))); }
        }
    }
    // corr-end

    // corr: crates/teamtype/src/types.rs :: TextDelta::insert
    pub fn insert(&mut self, s: &str)
        ensures final(self).v() == (if s@.len() != 0 { old(self).v().push(SOp::I(s@)) } else { old(self).v() }),
    {
        if num_chars(s) != 0 { // src: `!s.is_empty()`
            self.0.push(TextOp::Insert(to_owned(s))); // src: `s.to_string()`
            proof { assert(self.v() =~= old(self).v().push(SOp::I(s@))); }
        }
    }
    // corr-end

    // corr: crates/teamtype/src/types.rs :: TextDelta::delete
    pub fn delete(&mut self, n: usize)
        ensures final(self).v() == (if n != 0 { old(self).v().push(SOp::D(n as nat)) } else { old(self).v() }),
    {
        if n != 0 {
            self.0.push(TextOp::Delete(n));
            proof { assert(self.v() =~= old(self).v().push(SOp::D(n as nat))); }
        }
    }
    // corr-end

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

// src: `impl From<TextDelta> for OperationSeq { fn from(delta: TextDelta) -> Self }`
// corr: crates/teamtype/src/types.rs :: impl From<TextDelta> for OperationSeq
#[verifier::spinoff_prover] #[verifier::rlimit(100)]
pub fn delta_to_op_seq(delta: TextDelta) -> (r: OperationSeq)
    requires cons(delta.v()) <= MAXL, prod(delta.v()) <= MAXL,
    ensures
        r.wf(), r.base_len == cons(delta.v()), r.target_len == prod(delta.v()), ins(r.v()) == ins(delta.v()),
        forall|t: Seq<char>| t.len() == cons(delta.v()) ==> #[trigger] sem(t, r.v()) == sem(t, delta.v()),
{
    let mut op_seq = OperationSeq::default();
    // src: `for op in delta`
    let mut i: usize = 0;
    proof {
        assert(tvops(delta.0@.take(0)) =~= Seq::<SOp>::empty());
        assert(op_seq.v() =~= Seq::<SOp>::empty());
    }
    while i < delta.0.len()
        invariant
            i <= delta.0@.len(), cons(delta.v()) <= MAXL, prod(delta.v()) <= MAXL,
            op_seq.wf(),
            op_seq.base_len == cons(tvops(delta.0@.take(i as int))),
            op_seq.target_len == prod(tvops(delta.0@.take(i as int))),
            ins(op_seq.v()) == ins(tvops(delta.0@.take(i as int))),
            forall|t: Seq<char>| t.len() == op_seq.base_len ==> #[trigger] sem(t, op_seq.v()) == sem(t, tvops(delta.0@.take(i as int))),
        decreases delta.0@.len() - i,
    {
        let ghost p = tvops(delta.0@.take(i as int));
        let ghost o = tvop(delta.0@[i as int]);
        let ghost old_seq = op_seq;
        proof {
            assert(tvops(delta.0@.take(i + 1)) =~= p.push(o));
            assert(delta.v() =~= tvops(delta.0@.take(i + 1)) + tvops(delta.0@.skip(i + 1)));
            lemma_add(tvops(delta.0@.take(i + 1)), tvops(delta.0@.skip(i + 1)));
            assert(p.push(o).drop_last() =~= p);
            lemma_add(p, seq![o]);
            assert(p + seq![o] =~= p.push(o));
            lemma_one(blank(cons_of(o) as int), o);
        }
        match &delta.0[i] {
            TextOp::Retain(n) => { op_seq.retain(*n as u64); }
            TextOp::Insert(s) => { op_seq.insert(s.as_str()); }
            TextOp::Delete(n) => { op_seq.delete(*n as u64); }
        }
        proof {
            assert forall|t: Seq<char>| t.len() == op_seq.base_len implies #[trigger] sem(t, op_seq.v()) == sem(t, p.push(o)) by {
                assert(t.take(old_seq.base_len as int).len() == old_seq.base_len);
                assert(sem(t.take(old_seq.base_len as int), old_seq.v()) == sem(t.take(old_seq.base_len as int), p));
                if o is I {
                    assert(t.take(old_seq.base_len as int) =~= t);
                    assert(sem(t, old_seq.v()) == sem(t, p));
                    assert(t.skip(cons(p) as int).len() == 0);
                }
            }
        }
        i += 1;
    }
    proof { assert(delta.0@.take(i as int) =~= delta.0@); }
    op_seq
}
// corr-end

// src: `impl From<OperationSeq> for TextDelta { fn from(op_seq: OperationSeq) -> Self }`
// corr: crates/teamtype/src/types.rs :: impl From<OperationSeq> for TextDelta
pub fn op_seq_to_delta(op_seq: OperationSeq) -> (r: TextDelta)
    requires op_seq.wf(),
    ensures r.v() == op_seq.v(),
{
    let mut delta = TextDelta::default();
    // src: `for op in op_seq.ops()`
    let mut i: usize = 0;
    while i < op_seq.ops.len()
        invariant op_seq.wf(), i <= op_seq.ops@.len(), delta.v() == vops(op_seq.ops@.take(i as int)),
        decreases op_seq.ops@.len() - i,
    {
        proof {
            assert(vops(op_seq.ops@.take(i + 1)) =~= vops(op_seq.ops@.take(i as int)).push(vop(op_seq.ops@[i as int])));
            assert(nz(op_seq.v()[i as int]));
        }
        match &op_seq.ops[i] {
            Operation::Retain(n) => { delta.retain(*n as usize); }
            Operation::Insert(s) => { delta.insert(s.as_str()); }
            Operation::Delete(n) => { delta.delete(*n as usize); }
        }
        i += 1;
    }
    proof { assert(op_seq.ops@.take(i as int) =~= op_seq.ops@); }
    delta
}
// corr-end

// ---------- editor-side types; position conversion trusted (ASSUMED) ----------
pub struct Error;

pub struct Position { pub line: usize, pub character: usize }

pub uninterp spec fn line_start(t: Seq<char>, line: int) -> int;
pub uninterp spec fn line_at(t: Seq<char>, at: int) -> int;
pub uninterp spec fn line_count(t: Seq<char>) -> int;
#[verifier::external_body]
pub struct Rope { inner: () }
impl Rope {
    pub uninterp spec fn view(&self) -> Seq<char>;
    #[verifier::external_body]
    pub fn from_str(t: &str) -> (r: Rope)
        ensures r@ == t@,
    { unimplemented!() }
    #[verifier::external_body]
    pub fn try_char_to_line(&self, at: usize) -> (r: Result<usize, Error>)
        ensures
            at > self@.len() ==> r is Err,
            at <= self@.len() ==> (r matches Ok(l) && l == line_at(self@, at as int)
                && 0 <= l < line_count(self@)
                && 0 <= line_start(self@, l as int) <= at),
    { unimplemented!() }
    #[verifier::external_body]
    pub fn try_line_to_char(&self, l: usize) -> (r: Result<usize, Error>)
        requires l < line_count(self@),
        ensures r matches Ok(at) && at == line_start(self@, l as int),
    { unimplemented!() }
}
pub open spec fn offset(t: Seq<char>, p: Position) -> int {
    line_start(t, p.line as int) + p.character
}

// src: `Position::try_from_offset(o, content)`. Spec proved for the real code in
// ../positions/REFINEMENT.md ("try_from_offset(o) succeeds exactly when o <= N"),
// relative to that file's Ropey model; trusted here.
pub fn position_try_from_offset(o: usize, content: &str) -> (r: Result<Position, Error>)
    ensures r is Ok <==> o <= content@.len(),
        r matches Ok(p) ==> offset(content@, p) == o,
{
    let rope = Rope::from_str(content);
    let line = match rope.try_char_to_line(o) { Ok(l) => l, Err(e) => return Err(e) };
    let at = match rope.try_line_to_char(line) { Ok(a) => a, Err(e) => return Err(e) };
    let character = o - at;
    Ok(Position { line, character })
}

pub struct Range { pub start: Position, pub end: Position }
pub struct EditorTextOp { pub range: Range, pub replacement: String }
pub struct EditorTextDelta(pub Vec<EditorTextOp>);

pub struct Edit { pub start: int, pub end: int, pub text: Seq<char> }
pub open spec fn edits(t: Seq<char>, d: EditorTextDelta) -> Seq<Edit> {
    d.0@.map_values(|e: EditorTextOp| Edit {
        start: offset(t, e.range.start), end: offset(t, e.range.end), text: e.replacement@
    })
}
pub open spec fn emitted(p: Seq<SOp>) -> Seq<Edit> decreases p.len() {
    if p.len() == 0 { seq![] } else {
        let a = emitted(p.drop_last());
        let at = cons(p.drop_last()) as int;
        match p.last() {
            SOp::R(_) => a,
            SOp::D(n) => a.push(Edit { start: at, end: at + n, text: seq![] }),
            SOp::I(s) => a.push(Edit { start: at, end: at, text: s }),
        }
    }
}
pub open spec fn cursor(es: Seq<Edit>) -> int {
    if es.len() == 0 { 0 } else { es.last().end }
}
pub open spec fn edits_wf(es: Seq<Edit>, bound: int) -> bool decreases es.len() {
    if es.len() == 0 { 0 <= bound } else {
        &&& edits_wf(es.drop_last(), es.last().start)
        &&& cursor(es.drop_last()) <= es.last().start
        &&& 0 <= es.last().start <= es.last().end <= bound
    }
}
pub open spec fn rendered(t: Seq<char>, es: Seq<Edit>) -> Seq<char> decreases es.len() {
    if es.len() == 0 { seq![] } else {
        let prev = es.drop_last(); let e = es.last();
        rendered(t, prev) + t.subrange(cursor(prev), e.start) + e.text
    }
}
pub open spec fn editor_apply(t: Seq<char>, d: EditorTextDelta) -> Seq<char> {
    let es = edits(t, d);
    rendered(t, es) + t.skip(cursor(es))
}

pub proof fn emitted_semantics(t: Seq<char>, p: Seq<SOp>)
    requires cons(p) <= t.len(),
    ensures
        edits_wf(emitted(p), cons(p) as int),
        0 <= cursor(emitted(p)) <= cons(p),
        rendered(t, emitted(p)) + t.subrange(cursor(emitted(p)), cons(p) as int)
            == sem(t.take(cons(p) as int), p),
        rendered(t, emitted(p)) + t.skip(cursor(emitted(p))) == fsem(t, p),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(t.take(0) =~= Seq::<char>::empty());
        assert(t.skip(0) =~= t);
    } else {
        let q = p.drop_last(); let c = cons(q) as int;
        emitted_semantics(t, q);
        assert(t.take(cons(p) as int).take(c) =~= t.take(c));
        assert(t.take(cons(p) as int).skip(c) =~= t.subrange(c, cons(p) as int));
        match p.last() {
            SOp::R(_) => {
                edits_wf_extend(emitted(q), c, cons(p) as int);
                assert(t.subrange(cursor(emitted(q)), c) + t.subrange(c, cons(p) as int)
                    =~= t.subrange(cursor(emitted(q)), cons(p) as int));
            },
            SOp::D(_) | SOp::I(_) => {
                assert(emitted(p).drop_last() =~= emitted(q));
            },
        }
    }
    assert(t.subrange(cursor(emitted(p)), cons(p) as int) + t.skip(cons(p) as int)
        =~= t.skip(cursor(emitted(p))));
}

pub proof fn edits_wf_extend(es: Seq<Edit>, a: int, b: int)
    requires edits_wf(es, a), a <= b,
    ensures edits_wf(es, b),
{}

// src: `EditorTextDelta::try_from_delta(delta: TextDelta, content: &str) -> Result<Self>`
// corr: crates/teamtype/src/types.rs :: EditorTextDelta::try_from_delta
pub fn try_from_delta(delta: TextDelta, content: &str) -> (r: Result<EditorTextDelta, Error>)
    requires cons(delta.v()) <= MAXL,
    ensures cons(delta.v()) <= content@.len() ==> r is Ok,
        r matches Ok(d) ==> edits(content@, d) == emitted(delta.v()),
        cons(delta.v()) <= content@.len() && r is Ok ==>
            editor_apply(content@, r->Ok_0) == fsem(content@, delta.v()),
        cons(delta.v()) <= content@.len() && r is Ok ==>
            edits_wf(edits(content@, r->Ok_0), content@.len() as int),
{
    let mut editor_ops: Vec<EditorTextOp> = Vec::new();
    let mut position: usize = 0;
    // src: `for op in delta`
    let mut i: usize = 0;
    proof { assert(tvops(delta.0@.take(0)) =~= Seq::<SOp>::empty()); }
    while i < delta.0.len()
        invariant
            i <= delta.0@.len(), cons(delta.v()) <= MAXL,
            position == cons(tvops(delta.0@.take(i as int))),
            edits(content@, EditorTextDelta(editor_ops)) == emitted(tvops(delta.0@.take(i as int))),
        decreases delta.0@.len() - i,
    {
        proof {
            let p = tvops(delta.0@.take(i as int));
            let o = tvop(delta.0@[i as int]);
            assert(tvops(delta.0@.take(i + 1)) =~= p.push(o));
            assert(p.push(o).drop_last() =~= p);
            assert(delta.v() =~= tvops(delta.0@.take(i + 1)) + tvops(delta.0@.skip(i + 1)));
            lemma_add(tvops(delta.0@.take(i + 1)), tvops(delta.0@.skip(i + 1)));
        }
        match &delta.0[i] {
            TextOp::Retain(n) => position += *n,
            TextOp::Delete(n) => {
                // src: `start: Position::try_from_offset(position, content)?,` (and `end` likewise)
                let start = match position_try_from_offset(position, content) { Ok(p) => p, Err(e) => return Err(e) };
                let end = match position_try_from_offset(position + *n, content) { Ok(p) => p, Err(e) => return Err(e) };
                editor_ops.push(EditorTextOp { range: Range { start, end }, replacement: String::new() });
                position += *n;
            }
            TextOp::Insert(s) => {
                let start = match position_try_from_offset(position, content) { Ok(p) => p, Err(e) => return Err(e) };
                let end = match position_try_from_offset(position, content) { Ok(p) => p, Err(e) => return Err(e) };
                editor_ops.push(EditorTextOp { range: Range { start, end }, replacement: s.clone() });
            }
        }
        i += 1;
    }
    proof {
        assert(tvops(delta.0@.take(i as int)) =~= delta.v());
        if cons(delta.v()) <= content@.len() {
            emitted_semantics(content@, delta.v());
            edits_wf_extend(emitted(delta.v()), cons(delta.v()) as int, content@.len() as int);
        }
    }
    Ok(EditorTextDelta(editor_ops))
}
// corr-end

pub struct RevisionedEditorTextDelta { pub revision: usize, pub delta: EditorTextDelta }
pub struct RevisionedTextDelta { pub revision: usize, pub delta: TextDelta }

#[verifier::opaque]
pub open spec fn outputs_correct(s: &OTServer, ds: Seq<RevisionedEditorTextDelta>) -> bool {
    &&& ds.len() == s.editor_queue@.len()
    &&& forall|j: int| 0 <= j < ds.len() ==> {
        &&& (#[trigger] ds[j]).revision == s.editor_revision
        &&& edits_wf(edits(chain(s.last_confirmed_editor_content@, s.editor_queue@.take(j)), ds[j].delta),
            chain(s.last_confirmed_editor_content@, s.editor_queue@.take(j)).len() as int)
        &&& editor_apply(chain(s.last_confirmed_editor_content@, s.editor_queue@.take(j)), ds[j].delta)
            == chain(s.last_confirmed_editor_content@, s.editor_queue@.take(j + 1))
    }
}

pub open spec fn editor_chain(t: Seq<char>, ds: Seq<RevisionedEditorTextDelta>) -> Seq<char>
    decreases ds.len(),
{
    if ds.len() == 0 { t } else { editor_apply(editor_chain(t, ds.drop_last()), ds.last().delta) }
}

pub proof fn outputs_prefix(s: &OTServer, ds: Seq<RevisionedEditorTextDelta>, n: int)
    requires outputs_correct(s, ds), 0 <= n <= ds.len(),
    ensures editor_chain(s.last_confirmed_editor_content@, ds.take(n))
        == chain(s.last_confirmed_editor_content@, s.editor_queue@.take(n)),
    decreases n,
{
    reveal(outputs_correct);
    if n == 0 {
        assert(ds.take(n) =~= Seq::<RevisionedEditorTextDelta>::empty());
        assert(s.editor_queue@.take(n) =~= Seq::<OperationSeq>::empty());
    } else {
        outputs_prefix(s, ds, n - 1);
        assert(ds.take(n).drop_last() =~= ds.take(n - 1));
        assert(ds.take(n).last() == ds[n - 1]);
    }
}

pub proof fn outputs_converge(s: &OTServer, ds: Seq<RevisionedEditorTextDelta>)
    requires s.inv(), outputs_correct(s, ds),
    ensures editor_chain(s.last_confirmed_editor_content@, ds) == s.current_content@,
{
    reveal(outputs_correct);
    outputs_prefix(s, ds, ds.len() as int);
    assert(ds.take(ds.len() as int) =~= ds);
    assert(s.editor_queue@.take(ds.len() as int) =~= s.editor_queue@);
}

// src: `RevisionedTextDelta::try_from_rev_ed_delta(rev_ed_delta, content) -> Result<Self>`.
// Not verified (it calls TextDelta::compose and Range::as_relative). ASSUMED: on
// success, the delta fits the content and has no zero-length ops.
#[verifier::external_body]
pub fn try_from_rev_ed_delta(rev_ed_delta: RevisionedEditorTextDelta, content: &str) -> (r: Result<RevisionedTextDelta, Error>)
    ensures r is Ok ==> cons(r->Ok_0.delta.v()) <= content@.len(),
{ unimplemented!() }

// src: `self.editor_queue.drain(..seen_operations)` (std Vec::drain, ASSUMED)
#[verifier::external_body]
pub fn drain_front(v: &mut Vec<OperationSeq>, n: usize) -> (r: Vec<OperationSeq>)
    requires n <= old(v)@.len(),
    ensures r@ == old(v)@.take(n as int), final(v)@ == old(v)@.skip(n as int),
{ v.drain(..n).collect() }

// ======================= real code: teamtype source/ot.rs OTServer =======================

#[verifier::spinoff_prover] #[verifier::rlimit(100)]
pub proof fn lemma_chain_app(u: Seq<char>, p: Seq<OperationSeq>, q: Seq<OperationSeq>)
    ensures
        chain(u, p + q) == chain(chain(u, p), q),
        (chain_ok(u, p) && chain_ok(chain(u, p), q)) <==> chain_ok(u, p + q),
{
    lemma_chain_app_take(u, p, q, q.len() as int);
    assert(q.take(q.len() as int) =~= q);
    let pq = p + q;
    assert forall|i: int| 0 <= i < p.len() implies #[trigger] pq.take(i) == p.take(i) by {
        assert(pq.take(i) =~= p.take(i));
    }
    assert forall|j: int| 0 <= j < q.len() implies chain(u, #[trigger] pq.take(p.len() + j)) == chain(chain(u, p), q.take(j)) by {
        assert(pq.take(p.len() + j) =~= p + q.take(j));
        lemma_chain_app_take(u, p, q, j);
    }
    if chain_ok(u, p) && chain_ok(chain(u, p), q) {
        assert forall|i: int| 0 <= i < pq.len() implies #[trigger] pq[i].wf() && pq[i].base_len <= chain(u, pq.take(i)).len() by {
            if i >= p.len() {
                let j = i - p.len();
                assert(pq[i] == q[j]);
                assert(q[j].wf());
                assert(chain(u, pq.take(p.len() + j)) == chain(chain(u, p), q.take(j)));
            } else {
                assert(pq[i] == p[i]);
                assert(p[i].wf());
                assert(pq.take(i) == p.take(i));
            }
        }
        assert(chain_ok(u, pq));
    }
    if chain_ok(u, pq) {
        assert forall|i: int| 0 <= i < p.len() implies #[trigger] p[i].wf() && p[i].base_len <= chain(u, p.take(i)).len() by {
            assert(pq[i] == p[i]);
            assert(pq[i].wf() && pq[i].base_len <= chain(u, pq.take(i)).len());
            assert(pq.take(i) == p.take(i));
        }
        assert forall|j: int| 0 <= j < q.len() implies #[trigger] q[j].wf() && q[j].base_len <= chain(chain(u, p), q.take(j)).len() by {
            let i = p.len() + j;
            assert(pq[i] == q[j]);
            assert(pq[i].wf() && pq[i].base_len <= chain(u, pq.take(i)).len());
            assert(chain(u, pq.take(p.len() + j)) == chain(chain(u, p), q.take(j)));
        }
    }
}

pub proof fn lemma_chain_app_take(u: Seq<char>, p: Seq<OperationSeq>, q: Seq<OperationSeq>, i: int)
    requires 0 <= i <= q.len(),
    ensures chain(u, p + q.take(i)) == chain(chain(u, p), q.take(i)),
    decreases i,
{
    if i == 0 {
        assert(p + q.take(0) =~= p);
        assert(q.take(0) =~= Seq::<OperationSeq>::empty());
    } else {
        lemma_chain_app_take(u, p, q, i - 1);
        assert((p + q.take(i)).drop_last() =~= p + q.take(i - 1));
        assert(q.take(i).drop_last() =~= q.take(i - 1));
    }
}

pub struct OTServer {
    pub editor_revision: usize,
    pub daemon_revision: usize,
    pub operations: Vec<OperationSeq>,
    pub editor_queue: Vec<OperationSeq>,
    pub current_content: String,
    pub last_confirmed_editor_content: String,
}

impl OTServer {
    // The protocol invariant: the daemon's text is the editor's last confirmed
    // text with the not-yet-confirmed daemon operations applied in order, every
    // queued op fits the text it is applied to, the queue is no longer than the
    // daemon revision, and every intermediate text is below 2^60 characters.
    pub open spec fn inv(&self) -> bool {
        let lc = self.last_confirmed_editor_content@;
        let q = self.editor_queue@;
        &&& chain_ok(lc, q)
        &&& chain(lc, q) == self.current_content@
        &&& q.len() <= self.daemon_revision
        &&& forall|i: int| 0 <= i <= q.len() ==> (#[trigger] chain(lc, q.take(i))).len() <= L
    }

    // corr: crates/teamtype/src/ot.rs :: OTServer::new
    pub fn new(initial_content: String) -> (r: Self)
        requires initial_content@.len() <= L,
        ensures r.inv(),
    {
        // src: `last_confirmed_editor_content: initial_content.clone(), current_content: initial_content, ..Default::default()`
        let r = OTServer {
            last_confirmed_editor_content: initial_content.clone(),
            current_content: initial_content,
            editor_revision: 0, daemon_revision: 0, operations: Vec::new(), editor_queue: Vec::new(),
        };
        proof { assert forall|i: int| 0 <= i <= 0 implies (#[trigger] chain(r.last_confirmed_editor_content@, r.editor_queue@.take(i))).len() <= L by {
            assert(r.editor_queue@.take(i) =~= Seq::<OperationSeq>::empty());
        } }
        r
    }
    // corr-end

    // src: `pub fn apply_crdt_change(&mut self, delta: &TextDelta) -> Result<RevisionedEditorTextDelta>`
    #[verifier::spinoff_prover] #[verifier::rlimit(200)]
    pub fn apply_crdt_change(&mut self, delta: &TextDelta) -> (r: Result<RevisionedEditorTextDelta, Error>)
        requires
            old(self).inv(), old(self).daemon_revision < usize::MAX,
            cons(delta.v()) <= old(self).current_content@.len(),
            ins(delta.v()) <= L,
            // ASSUMED size bound on the resulting text (documents stay below 2^60 chars)
            prod(delta.v()) + old(self).current_content@.len() - cons(delta.v()) <= L,
        ensures r is Ok, final(self).inv(),
            final(self).current_content@ == fsem(old(self).current_content@, delta.v()),
    {
        proof {
            lemma_len(blank(cons(delta.v()) as int), delta.v());
            assert(old(self).editor_queue@.take(old(self).editor_queue@.len() as int) =~= old(self).editor_queue@);
            assert(chain(old(self).last_confirmed_editor_content@, old(self).editor_queue@.take(old(self).editor_queue@.len() as int)).len() <= L);
        }
        self.operations.push(delta_to_op_seq(delta.clone_delta()));
        self.editor_queue.push(delta_to_op_seq(delta.clone_delta()));
        self.daemon_revision += 1;
        // src: `.context("...")?`
        let editor_delta = match try_from_delta(delta.clone_delta(), self.current_content.as_str()) {
            Ok(d) => d,
            Err(e) => return Err(e),
        };
        let op = delta_to_op_seq(delta.clone_delta());
        proof {
            let lc = self.last_confirmed_editor_content@;
            let q0 = old(self).editor_queue@;
            let q = self.editor_queue@;
            let x = self.current_content@;
            assert(sem(x.take(cons(op.v()) as int), op.v()) == sem(x.take(cons(op.v()) as int), delta.v()));
            assert(q.drop_last() =~= q0);
            assert(q.take(q0.len() as int) =~= q0);
            assert(sem(x.take(cons(q.last().v()) as int), q.last().v()) == sem(x.take(cons(op.v()) as int), delta.v()));
            assert(fsem(x, q.last().v()) == fsem(x, op.v()));
            assert forall|i: int| 0 <= i < q.len() implies #[trigger] q[i].wf() && q[i].base_len <= chain(lc, q.take(i)).len() by {
                if i < q0.len() { assert(q.take(i) =~= q0.take(i)); }
            }
            lemma_fsem_len(x, op.v());
            assert forall|i: int| 0 <= i <= q.len() implies (#[trigger] chain(lc, q.take(i))).len() <= L by {
                if i <= q0.len() { assert(q.take(i) =~= q0.take(i)); } else { assert(q.take(i) =~= q); }
            }
        }
        self.current_content = force_apply(self.current_content.as_str(), op); // src: `delta.clone().into()`

        Ok(RevisionedEditorTextDelta {
            revision: self.editor_revision,
            delta: editor_delta,
        })
    }

    // Model of commit e28f9e0 (branch verify-fixes) of the real fix:
    //   let op_seq: OperationSeq = delta.clone().into();
    //   if op_seq.base_len() > self.current_content.chars().count() { bail!(..) }
    //   let editor_delta = EditorTextDelta::try_from_delta(delta.clone(), &self.current_content).context(..)?;
    //   self.operations.push(op_seq.clone()); self.editor_queue.push(op_seq.clone());
    //   self.daemon_revision += 1;
    //   self.current_content = Self::force_apply(&self.current_content, op_seq);
    // No precondition that the delta fits. Size preconditions only (see REFINEMENT.md).
    // corr: crates/teamtype/src/ot.rs :: OTServer::apply_crdt_change
    #[verifier::spinoff_prover] #[verifier::rlimit(200)]
    pub fn apply_crdt_change_fixed(&mut self, delta: &TextDelta) -> (r: Result<RevisionedEditorTextDelta, Error>)
        requires
            old(self).inv(), old(self).daemon_revision < usize::MAX,
            cons(delta.v()) <= MAXL, prod(delta.v()) <= MAXL, ins(delta.v()) <= L,
            // ASSUMED size bound on the resulting text, needed only when the delta fits
            cons(delta.v()) <= old(self).current_content@.len() ==>
                prod(delta.v()) + old(self).current_content@.len() - cons(delta.v()) <= L,
        ensures
            // (a) Err leaves all state unchanged
            r is Err ==> {
                &&& final(self).editor_revision == old(self).editor_revision
                &&& final(self).daemon_revision == old(self).daemon_revision
                &&& final(self).operations@ == old(self).operations@
                &&& final(self).editor_queue@ == old(self).editor_queue@
                &&& final(self).current_content@ == old(self).current_content@
                &&& final(self).last_confirmed_editor_content@ == old(self).last_confirmed_editor_content@
            },
            // a delta longer than the content is rejected
            cons(delta.v()) > old(self).current_content@.len() ==> r is Err,
            // (c) a fitting delta is accepted, with the original's postconditions
            cons(delta.v()) <= old(self).current_content@.len() ==> r is Ok,
            r is Ok ==> final(self).current_content@ == fsem(old(self).current_content@, delta.v()),
            r is Ok ==> final(self).daemon_revision == old(self).daemon_revision + 1,
            r is Ok ==> r->Ok_0.revision == old(self).editor_revision,
            r is Ok ==> editor_apply(old(self).current_content@, r->Ok_0.delta)
                == final(self).current_content@,
            r is Ok ==> edits_wf(edits(old(self).current_content@, r->Ok_0.delta),
                old(self).current_content@.len() as int),
            // invariant holds on both paths
            final(self).inv(),
    {
        let op_seq = delta_to_op_seq(delta.clone_delta()); // src: `delta.clone().into()`
        // src: `op_seq.base_len() > self.current_content.chars().count()` then `bail!`
        if op_seq.base_len > num_chars(self.current_content.as_str()) {
            return Err(Error);
        }
        // src: `.context("...")?`
        let editor_delta = match try_from_delta(delta.clone_delta(), self.current_content.as_str()) {
            Ok(d) => d,
            Err(e) => return Err(e),
        };
        proof {
            lemma_len(blank(cons(delta.v()) as int), delta.v());
            assert(old(self).editor_queue@.take(old(self).editor_queue@.len() as int) =~= old(self).editor_queue@);
            assert(chain(old(self).last_confirmed_editor_content@, old(self).editor_queue@.take(old(self).editor_queue@.len() as int)).len() <= L);
        }
        self.operations.push(op_seq.clone_seq());
        self.editor_queue.push(op_seq.clone_seq());
        self.daemon_revision += 1;
        proof {
            let lc = self.last_confirmed_editor_content@;
            let q0 = old(self).editor_queue@;
            let q = self.editor_queue@;
            let x = self.current_content@;
            assert(q.drop_last() =~= q0);
            assert(q.take(q0.len() as int) =~= q0);
            assert forall|i: int| 0 <= i < q.len() implies #[trigger] q[i].wf() && q[i].base_len <= chain(lc, q.take(i)).len() by {
                if i < q0.len() { assert(q.take(i) =~= q0.take(i)); }
            }
            lemma_fsem_len(x, op_seq.v());
            assert forall|i: int| 0 <= i <= q.len() implies (#[trigger] chain(lc, q.take(i))).len() <= L by {
                if i <= q0.len() { assert(q.take(i) =~= q0.take(i)); } else { assert(q.take(i) =~= q); }
            }
        }
        self.current_content = force_apply(self.current_content.as_str(), op_seq);

        Ok(RevisionedEditorTextDelta {
            revision: self.editor_revision,
            delta: editor_delta,
        })
    }
    // corr-end

    // src: `pub fn apply_editor_operation(&mut self, rev_editor_delta) -> Result<(TextDelta, Vec<RevisionedEditorTextDelta>)>`
    // corr: crates/teamtype/src/ot.rs :: OTServer::apply_editor_operation
    #[verifier::spinoff_prover] #[verifier::rlimit(100)]
    pub fn apply_editor_operation(&mut self, rev_editor_delta: RevisionedEditorTextDelta)
        -> (r: Result<(TextDelta, Vec<RevisionedEditorTextDelta>), Error>)
        requires
            old(self).inv(), old(self).editor_revision < usize::MAX,
            // the editor acknowledges a daemon revision it can have seen ...
            rev_editor_delta.revision <= old(self).daemon_revision,
            // ... and not older than one it already acknowledged
            old(self).daemon_revision - rev_editor_delta.revision <= old(self).editor_queue@.len(),
        ensures final(self).inv(),
            final(self).editor_revision == old(self).editor_revision + 1,
            r is Ok ==> cons(r->Ok_0.0.v()) <= old(self).current_content@.len(),
            r is Ok ==> fsem(old(self).current_content@, r->Ok_0.0.v()) == final(self).current_content@,
            r is Ok ==> outputs_correct(final(self), r->Ok_0.1@),
    {
        let daemon_revision = rev_editor_delta.revision;
        self.editor_revision += 1;

        // src: `assert!(daemon_revision <= self.daemon_revision, "...")`
        if !(daemon_revision <= self.daemon_revision) { return Err(Error); }

        let daemon_operations_to_transform = self.daemon_revision - daemon_revision;
        // src: `assert!(self.editor_queue.len() >= daemon_operations_to_transform, "...")`
        if !(self.editor_queue.len() >= daemon_operations_to_transform) { return Err(Error); }
        let seen_operations = self.editor_queue.len() - daemon_operations_to_transform;
        // src: `debug!(..)` and `warn!(..)` logging omitted
        let ghost lc0 = self.last_confirmed_editor_content@;
        let ghost q0 = self.editor_queue@;
        let confirmed_queue = drain_front(&mut self.editor_queue, seen_operations);
        proof {
            assert(q0 =~= confirmed_queue@ + self.editor_queue@);
            lemma_chain_app(lc0, confirmed_queue@, self.editor_queue@);
        }
        // src: `for confirmed_editor_op in confirmed_queue`
        let mut j: usize = 0;
        proof { assert(confirmed_queue@.take(0) =~= Seq::<OperationSeq>::empty()); }
        while j < confirmed_queue.len()
            invariant
                j <= confirmed_queue@.len(),
                q0 == confirmed_queue@ + self.editor_queue@,
                chain_ok(lc0, confirmed_queue@),
                chain_ok(lc0, q0),
                forall|i: int| 0 <= i <= q0.len() ==> (#[trigger] chain(lc0, q0.take(i))).len() <= L,
                self.last_confirmed_editor_content@ == chain(lc0, confirmed_queue@.take(j as int)),
                self.current_content@ == old(self).current_content@,
                self.editor_revision == old(self).editor_revision + 1,
            decreases confirmed_queue@.len() - j,
        {
            let ghost cq = confirmed_queue@;
            proof {
                assert(cq[j as int].wf());
                assert(cq.take(j + 1).drop_last() =~= cq.take(j as int));
                assert(cq.take(j + 1).last() == cq[j as int]);
                assert(q0.take(j as int) =~= cq.take(j as int));
                assert(q0.take(j + 1) =~= cq.take(j + 1));
                lemma_fsem_len(self.last_confirmed_editor_content@, cq[j as int].v());
                assert(chain(lc0, q0.take(j + 1)).len() <= L);
            }
            self.last_confirmed_editor_content = force_apply(
                self.last_confirmed_editor_content.as_str(),
                confirmed_queue[j].clone_seq(),
            );
            j += 1;
        }
        let ghost lcd = self.last_confirmed_editor_content@;
        proof {
            assert(confirmed_queue@.take(j as int) =~= confirmed_queue@);
            let p = confirmed_queue@;
            let q = self.editor_queue@;
            assert forall|i: int| 0 <= i <= q.len() implies (#[trigger] chain(lcd, q.take(i))).len() <= L by {
                lemma_chain_app_take(lc0, p, q, i);
                assert((p + q).take(p.len() + i) =~= p + q.take(i));
                assert(chain(lc0, q0.take(p.len() + i)).len() <= L);
            }
            assert(q.len() == daemon_operations_to_transform);
        }
        // src: `RevisionedTextDelta::try_from_rev_ed_delta(..).context("...")?`
        let rev_delta = match try_from_rev_ed_delta(rev_editor_delta, self.last_confirmed_editor_content.as_str()) {
            Ok(d) => d,
            Err(e) => return Err(e),
        };
        // ASSUMED size bound: the editor's inserted text and the resulting
        // texts stay below 2^60 characters (see REFINEMENT.md, "Assumed").
        proof { assume(ins(rev_delta.delta.v()) <= L && prod(rev_delta.delta.v()) <= L); }
        let mut op_seq = delta_to_op_seq(rev_delta.delta);
        proof { lemma_fsem_len(lcd, op_seq.v()); }

        self.last_confirmed_editor_content = force_apply(self.last_confirmed_editor_content.as_str(), op_seq.clone_seq());
        proof {
            assert(self.last_confirmed_editor_content@ == fsem(lcd, op_seq.v()));
        }
        let ghost q = self.editor_queue@;
        let ghost docs = Seq::new((q.len() + 1) as nat, |i: int| chain(lcd, q.take(i)));
        proof {
            assert(docs[0] == lcd) by { assert(q.take(0) =~= Seq::<OperationSeq>::empty()); }
            assert(docs.last() == chain(lcd, q)) by { assert(q.take(q.len() as int) =~= q); }
            assert forall|i: int| 0 <= i < q.len() implies {
                &&& (#[trigger] q[i]).wf()
                &&& q[i].base_len <= docs[i].len()
                &&& docs[i + 1] == fsem(docs[i], q[i].v())
            } by {
                assert(q.take(i + 1).drop_last() =~= q.take(i));
                assert(q.take(i + 1).last() == q[i]);
                assert(docs[i] == chain(lcd, q.take(i)));
                assert(docs[i + 1] == chain(lcd, q.take(i + 1)));
                assert(chain_ok(lcd, q));
                assert(q[i].wf() && q[i].base_len <= chain(lcd, q.take(i)).len());
            }
            assert forall|i: int| 0 <= i < docs.len() implies (#[trigger] docs[i]).len() <= L by {}
        }
        let (op2, queue2) = transform_through_operations(op_seq, self.editor_queue.as_slice(), Ghost(docs));
        op_seq = op2;
        self.editor_queue = queue2;
        // src: `(op_seq, self.editor_queue) = transform_through_operations(op_seq, &self.editor_queue);`
        self.operations.push(op_seq.clone_seq());
        // ASSUMED size bound on the new texts (documents stay below 2^60 chars)
        proof {
            let lc = self.last_confirmed_editor_content@;
            let nq = self.editor_queue@;
            assume(forall|i: int| 0 <= i <= nq.len() ==> (#[trigger] chain(lc, nq.take(i))).len() <= L);
            assert(nq.take(nq.len() as int) =~= nq);
            lemma_fsem_len(self.current_content@, op_seq.v());
        }
        self.current_content = force_apply(self.current_content.as_str(), op_seq.clone_seq());
        let deltas_for_editor = self.deltas_for_editor();
        proof {
            assert(fsem(old(self).current_content@, op_seq.v()) == self.current_content@);
            assert(outputs_correct(self, deltas_for_editor@));
        }
        Ok((op_seq_to_delta(op_seq), deltas_for_editor))
    }
    // corr-end

    // src: `fn deltas_for_editor(&self) -> Vec<RevisionedEditorTextDelta>`
    // corr: crates/teamtype/src/ot.rs :: OTServer::deltas_for_editor
    #[verifier::spinoff_prover] #[verifier::rlimit(100)]
    pub fn deltas_for_editor(&self) -> (r: Vec<RevisionedEditorTextDelta>)
        requires self.inv(),
        ensures r@.len() == self.editor_queue@.len(),
            outputs_correct(self, r@),
    {
        reveal(outputs_correct);
        let mut to_editor: Vec<RevisionedEditorTextDelta> = Vec::new();
        let mut document = self.last_confirmed_editor_content.clone();
        let ghost lc = self.last_confirmed_editor_content@;
        let ghost q = self.editor_queue@;
        // src: `for editor_op in &self.editor_queue`
        let mut i: usize = 0;
        proof { assert(q.take(0) =~= Seq::<OperationSeq>::empty()); }
        while i < self.editor_queue.len()
            invariant
                self.inv(), lc == self.last_confirmed_editor_content@, q == self.editor_queue@,
                i <= q.len(), to_editor@.len() == i,
                document@ == chain(lc, q.take(i as int)),
                forall|j: int| 0 <= j < i ==> {
                    &&& (#[trigger] to_editor@[j]).revision == self.editor_revision
                    &&& edits_wf(edits(chain(lc, q.take(j)), to_editor@[j].delta), chain(lc, q.take(j)).len() as int)
                    &&& editor_apply(chain(lc, q.take(j)), to_editor@[j].delta) == chain(lc, q.take(j + 1))
                },
            decreases q.len() - i,
        {
            proof {
                assert(q[i as int].wf());
                assert(q.take(i + 1).drop_last() =~= q.take(i as int));
                assert(q.take(i + 1).last() == q[i as int]);
                assert(chain(lc, q.take(i + 1)).len() <= L);
                lemma_fsem_len(document@, q[i as int].v());
            }
            let delta: TextDelta = op_seq_to_delta(self.editor_queue[i].clone_seq());
            // src: `EditorTextDelta::try_from_delta(delta, &document).expect("...")`
            let ed_delta = match try_from_delta(delta, document.as_str()) {
                Ok(d) => d,
                Err(_) => unreachable_panic(),
            };
            to_editor.push(RevisionedEditorTextDelta { revision: self.editor_revision, delta: ed_delta }); // src: `RevisionedEditorTextDelta::new(..)`
            assert(to_editor@[i as int].revision == self.editor_revision);

            document = force_apply(document.as_str(), self.editor_queue[i].clone_seq());
            i += 1;
        }
        to_editor
    }
    // corr-end
}

fn main() {}
}
