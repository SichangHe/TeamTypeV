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


/// Execute both sides of TP1 using the verified transform and apply bodies.
pub fn tp1(a: &OperationSeq, b: &OperationSeq, s: &str) -> (r: (String, String))
    requires a.wf(), b.wf(), a.base_len == b.base_len,
        s@.len() == a.base_len, a.target_len + b.target_len <= MAXL,
    ensures r.0@ == r.1@,
        r.0@.len() <= a.target_len + b.target_len,
{
    let (ap, bp) = match a.transform(b, Ghost(s@)) {
        Ok(p) => p, Err(_) => unreachable_panic(),
    };
    let sa = match a.apply(s) { Ok(t) => t, Err(_) => unreachable_panic() };
    let sb = match b.apply(s) { Ok(t) => t, Err(_) => unreachable_panic() };
    proof { lemma_len(s@, a.v()); lemma_len(s@, b.v()); }
    let left = match bp.apply(sa.as_str()) { Ok(t) => t, Err(_) => unreachable_panic() };
    let right = match ap.apply(sb.as_str()) { Ok(t) => t, Err(_) => unreachable_panic() };
    proof { lemma_len(sa@, bp.v()); }
    (left, right)
}
}
fn main() {}
