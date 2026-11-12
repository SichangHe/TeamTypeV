mod conc {
// Verus model of TeamType's editor/daemon concurrency: protocol model + refinement of the real
// `OTServer` (see DESIGN.md). Sections: (1) trusted OT model, (2) protocol model and its proofs,
// (3) refinement of ot.rs bodies against the model's transitions.
use vstd::prelude::*;

verus! {

// ---------- trusted operational-transform model (ASSUMED) ----------
// ops are opaque; ap(d, o) = text after applying o (what `force_apply` computes, incl. its padding).
pub uninterp spec fn ap(d: Seq<char>, o: int) -> Seq<char>;
pub uninterp spec fn tr_my(m: int, t: int) -> int;    // m' of m.transform(t)
pub uninterp spec fn tr_their(m: int, t: int) -> int; // t' of m.transform(t)
pub uninterp spec fn pad(o: int, n: nat) -> int;      // o after o.retain(n)
pub uninterp spec fn base_len_of(o: int) -> nat;

// TP1: m then t' == t then m'   (ASSUMED; unconditional in this model, the real crate needs
// equal base lengths, which `transform_through_operations` establishes by padding)
#[verifier::external_body]
pub proof fn axiom_tp1(d: Seq<char>, m: int, t: int)
    ensures ap(ap(d, m), tr_their(m, t)) == ap(ap(d, t), tr_my(m, t)),
{}

// a trailing retain does not change the result of force_apply (ASSUMED)
#[verifier::external_body]
pub proof fn axiom_pad(d: Seq<char>, o: int, n: nat)
    ensures ap(d, pad(o, n)) == ap(d, o),
{}

pub open spec fn fold(d: Seq<char>, q: Seq<int>) -> Seq<char>
    decreases q.len(),
{
    if q.len() == 0 { d } else { fold(ap(d, q[0]), q.drop_first()) }
}

pub proof fn lemma_fold_snoc(d: Seq<char>, q: Seq<int>, x: int)
    ensures fold(d, q.push(x)) == ap(fold(d, q), x),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(q.push(x).drop_first() =~= Seq::<int>::empty());
        assert(q.push(x)[0] == x);
        assert(fold(d, q.push(x)) == fold(ap(d, x), q.push(x).drop_first()));
        assert(fold(d, q) == d);
    } else {
        assert(q.push(x).drop_first() =~= q.drop_first().push(x));
        assert(q.push(x)[0] == q[0]);
        assert(fold(d, q.push(x)) == fold(ap(d, q[0]), q.push(x).drop_first()));
        assert(fold(d, q) == fold(ap(d, q[0]), q.drop_first()));
        lemma_fold_snoc(ap(d, q[0]), q.drop_first(), x);
    }
}

pub proof fn lemma_fold_split(d: Seq<char>, q: Seq<int>, k: int)
    requires 0 <= k <= q.len(),
    ensures fold(d, q) == fold(fold(d, q.subrange(0, k)), q.subrange(k, q.len() as int)),
    decreases k,
{
    if k == 0 {
        assert(q.subrange(0, 0) =~= Seq::<int>::empty());
        assert(q.subrange(0, q.len() as int) =~= q);
    } else {
        assert(q.subrange(0, k) =~= q.subrange(0, k - 1).push(q[k - 1]));
        lemma_fold_snoc(d, q.subrange(0, k - 1), q[k - 1]);
        lemma_fold_split(d, q, k - 1);
        let r = q.subrange(k - 1, q.len() as int);
        assert(r.drop_first() =~= q.subrange(k, q.len() as int));
    }
}

// the padding `transform_through_operations` does before each `transform`
pub open spec fn fix_m(m: int, t: int) -> int {
    if base_len_of(m) < base_len_of(t) { pad(m, (base_len_of(t) - base_len_of(m)) as nat) } else { m }
}
pub open spec fn fix_t(m: int, t: int) -> int {
    if base_len_of(m) < base_len_of(t) { t } else { pad(t, (base_len_of(m) - base_len_of(t)) as nat) }
}
pub proof fn lemma_fix(d: Seq<char>, m: int, t: int)
    ensures ap(d, fix_m(m, t)) == ap(d, m), ap(d, fix_t(m, t)) == ap(d, t),
{
    if base_len_of(m) < base_len_of(t) {
        axiom_pad(d, m, (base_len_of(t) - base_len_of(m)) as nat);
    } else {
        axiom_pad(d, t, (base_len_of(m) - base_len_of(t)) as nat);
    }
}

// transform_through_operations (their = o, my = q): returns (their', my')
pub open spec fn tt(o: int, q: Seq<int>) -> (int, Seq<int>)
    decreases q.len(),
{
    if q.len() == 0 {
        (o, Seq::empty())
    } else {
        let fm = fix_m(q[0], o);
        let ft = fix_t(q[0], o);
        let r = tt(tr_their(fm, ft), q.drop_first());
        (r.0, seq![tr_my(fm, ft)].add(r.1))
    }
}

pub proof fn lemma_tt(d: Seq<char>, o: int, q: Seq<int>)
    ensures
        tt(o, q).1.len() == q.len(),
        fold(ap(d, o), tt(o, q).1) == ap(fold(d, q), tt(o, q).0),
    decreases q.len(),
{
    if q.len() > 0 {
        let m = q[0];
        let fm = fix_m(m, o);
        let ft = fix_t(m, o);
        axiom_tp1(d, fm, ft);
        lemma_fix(d, m, o);
        lemma_fix(ap(d, o), m, o);
        lemma_tt(ap(d, m), tr_their(fm, ft), q.drop_first());
        let rest = tt(tr_their(fm, ft), q.drop_first()).1;
        assert(seq![tr_my(fm, ft)].add(rest).drop_first() =~= rest);
        assert(seq![tr_my(fm, ft)].add(rest)[0] == tr_my(fm, ft));
    }
}

// ---------- OTServer state (mirrors ot.rs fields; the history `operations` is not needed) ----------
pub struct Srv {
    pub er: nat,        // editor_revision
    pub dr: nat,        // daemon_revision
    pub q: Seq<int>,    // editor_queue
    pub lc: Seq<char>,  // last_confirmed_editor_content
    pub cur: Seq<char>, // current_content
}
pub struct Msg { pub rev: nat, pub op: int, pub g: nat } // daemon -> editor; g = absolute daemon-op index (ghost)
pub struct Up { pub rev: nat, pub op: int }             // editor -> daemon
pub struct Ed { pub buf: Seq<char>, pub rd: nat, pub re: nat } // plugin's revision.daemon / revision.editor

pub open spec fn confirmed(s: Srv) -> int { s.dr - s.q.len() }
pub open spec fn wf(s: Srv) -> bool { s.q.len() <= s.dr && fold(s.lc, s.q) == s.cur }

// messages for a queue: op i is sent with revision `rev` at absolute index g0 + i
pub open spec fn batch(q: Seq<int>, rev: nat, g0: nat) -> Seq<Msg>
    decreases q.len(),
{
    if q.len() == 0 { Seq::empty() } else {
        seq![Msg { rev, op: q[0], g: g0 }].add(batch(q.drop_first(), rev, g0 + 1))
    }
}

// OTServer::apply_crdt_change
pub open spec fn srv_crdt(s: Srv, o: int) -> (Srv, Msg) {
    (Srv { er: s.er, dr: s.dr + 1, q: s.q.push(o), lc: s.lc, cur: ap(s.cur, o) },
     Msg { rev: s.er, op: o, g: s.dr })
}

// OTServer::apply_editor_operation, for an edit that arrives with revision `rev` (a successful call)
pub open spec fn srv_edit(s: Srv, rev: nat, o: int) -> (Srv, Seq<Msg>) {
    let k = (rev - confirmed(s)) as int;
    let lc1 = fold(s.lc, s.q.subrange(0, k));
    let q1 = s.q.subrange(k, s.q.len() as int);
    let r = tt(o, q1);
    (Srv { er: s.er + 1, dr: s.dr, q: r.1, lc: ap(lc1, o), cur: ap(s.cur, r.0) },
     batch(r.1, s.er + 1, rev))
}

pub proof fn lemma_srv_edit_wf(s: Srv, rev: nat, o: int)
    requires wf(s), confirmed(s) <= rev <= s.dr,
    ensures wf(srv_edit(s, rev, o).0),
{
    let k = (rev - confirmed(s)) as int;
    let lc1 = fold(s.lc, s.q.subrange(0, k));
    let q1 = s.q.subrange(k, s.q.len() as int);
    lemma_fold_split(s.lc, s.q, k);
    lemma_tt(lc1, o, q1);
}

pub proof fn lemma_srv_crdt_wf(s: Srv, o: int)
    requires wf(s),
    ensures wf(srv_crdt(s, o).0),
{
    lemma_fold_snoc(s.lc, s.q, o);
}

// ---------- the world ----------
pub struct W { pub srv: Srv, pub ed: Ed, pub up: Seq<Up>, pub down: Seq<Msg> }

pub open spec fn up_ops(up: Seq<Up>) -> Seq<int> { up.map_values(|u: Up| u.op) }

// non-stale messages (rev == er) still in flight must cover absolute indices [from, to) in order
pub open spec fn covers(down: Seq<Msg>, er: nat, from: nat, to: nat) -> bool
    decreases down.len(),
{
    if down.len() == 0 { from == to } else {
        let m = down[0];
        if m.rev == er { m.g == from && from < to && covers(down.drop_first(), er, from + 1, to) }
        else { covers(down.drop_first(), er, from, to) }
    }
}

pub open spec fn inv(w: W) -> bool {
    let s = w.srv; let e = w.ed;
    let c = confirmed(s);
    &&& wf(s)
    &&& s.er <= e.re
    &&& w.up.len() == e.re - s.er
    &&& c <= e.rd <= s.dr
    &&& forall|i: int| 0 <= i < w.up.len() ==> (#[trigger] w.up[i]).rev == e.rd
    &&& e.buf == fold(fold(s.lc, s.q.subrange(0, e.rd - c)), up_ops(w.up))
    &&& forall|i: int| 0 <= i < w.down.len() ==> (#[trigger] w.down[i]).rev <= s.er
    &&& forall|i: int| 0 <= i < w.down.len() && (#[trigger] w.down[i]).rev == s.er ==>
            c <= w.down[i].g < s.dr && w.down[i].op == s.q[w.down[i].g - c]
    &&& (w.up.len() == 0 ==> covers(w.down, s.er, e.rd, s.dr))
}

// ---------- transitions ----------
pub open spec fn crdt_step(w: W, o: int) -> W {
    let r = srv_crdt(w.srv, o);
    W { srv: r.0, ed: w.ed, up: w.up, down: w.down.push(r.1) }
}
pub open spec fn ed_local(w: W, o: int) -> W {
    W { srv: w.srv,
        ed: Ed { buf: ap(w.ed.buf, o), rd: w.ed.rd, re: w.ed.re + 1 },
        up: w.up.push(Up { rev: w.ed.rd, op: o }), down: w.down }
}
pub open spec fn srv_recv(w: W) -> W {
    let u = w.up[0];
    let r = srv_edit(w.srv, u.rev, u.op);
    W { srv: r.0, ed: w.ed, up: w.up.drop_first(), down: w.down.add(r.1) }
}
pub open spec fn ed_recv(w: W) -> W {
    let m = w.down[0];
    if m.rev == w.ed.re {
        W { srv: w.srv, ed: Ed { buf: ap(w.ed.buf, m.op), rd: w.ed.rd + 1, re: w.ed.re },
            up: w.up, down: w.down.drop_first() }
    } else {
        W { srv: w.srv, ed: w.ed, up: w.up, down: w.down.drop_first() }
    }
}

// ---------- lemmas on batch / covers ----------
pub proof fn lemma_batch(q: Seq<int>, rev: nat, g0: nat)
    ensures
        batch(q, rev, g0).len() == q.len(),
        forall|i: int| 0 <= i < q.len() ==> (#[trigger] batch(q, rev, g0)[i]) == (Msg { rev, op: q[i], g: (g0 + i) as nat }),
    decreases q.len(),
{
    if q.len() > 0 {
        lemma_batch(q.drop_first(), rev, g0 + 1);
        let b = batch(q, rev, g0);
        let rest = batch(q.drop_first(), rev, g0 + 1);
        assert forall|i: int| 0 <= i < q.len() implies #[trigger] b[i] == (Msg { rev, op: q[i], g: (g0 + i) as nat }) by {
            if i > 0 {
                assert(b[i] == rest[i - 1]);
                assert(q.drop_first()[i - 1] == q[i]);
            }
        }
    }
}

pub proof fn lemma_covers_batch(q: Seq<int>, rev: nat, g0: nat)
    ensures covers(batch(q, rev, g0), rev, g0, g0 + q.len()),
    decreases q.len(),
{
    if q.len() > 0 {
        lemma_covers_batch(q.drop_first(), rev, g0 + 1);
        let b = batch(q, rev, g0);
        assert(b.drop_first() =~= batch(q.drop_first(), rev, g0 + 1));
    }
}

// a stale prefix does not matter
pub proof fn lemma_covers_stale_prefix(d1: Seq<Msg>, d2: Seq<Msg>, er: nat, from: nat, to: nat)
    requires forall|i: int| 0 <= i < d1.len() ==> (#[trigger] d1[i]).rev != er,
    ensures covers(d1.add(d2), er, from, to) == covers(d2, er, from, to),
    decreases d1.len(),
{
    if d1.len() == 0 {
        assert(d1.add(d2) =~= d2);
    } else {
        assert(d1.add(d2).drop_first() =~= d1.drop_first().add(d2));
        assert(d1[0].rev != er);
        assert forall|i: int| 0 <= i < d1.drop_first().len() implies (#[trigger] d1.drop_first()[i]).rev != er by {
            assert(d1.drop_first()[i] == d1[i + 1]);
        }
        lemma_covers_stale_prefix(d1.drop_first(), d2, er, from, to);
    }
}

// appending one expected non-stale message extends coverage; appending a stale one changes nothing
pub proof fn lemma_covers_push(down: Seq<Msg>, er: nat, from: nat, to: nat, m: Msg)
    requires covers(down, er, from, to), m.rev == er, m.g == to,
    ensures covers(down.push(m), er, from, to + 1),
    decreases down.len(),
{
    if down.len() == 0 {
        assert(down.push(m).drop_first() =~= Seq::<Msg>::empty());
        assert(down.push(m)[0] == m);
        assert(from == to);
        assert(covers(Seq::<Msg>::empty(), er, from + 1, to + 1));
    } else {
        assert(down.push(m).drop_first() =~= down.drop_first().push(m));
        assert(down.push(m)[0] == down[0]);
        if down[0].rev == er {
            lemma_covers_push(down.drop_first(), er, from + 1, to, m);
        } else {
            lemma_covers_push(down.drop_first(), er, from, to, m);
        }
    }
}

// ---------- the invariant is inductive ----------
pub proof fn lemma_crdt_step(w: W, o: int)
    requires inv(w),
    ensures inv(crdt_step(w, o)),
{
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let w2 = crdt_step(w, o);
    let s2 = w2.srv;
    lemma_srv_crdt_wf(s, o);
    assert(confirmed(s2) == c);
    assert(s.q.push(o).subrange(0, e.rd - c) =~= s.q.subrange(0, e.rd - c));
    assert forall|i: int| 0 <= i < w2.down.len() && (#[trigger] w2.down[i]).rev == s2.er
        implies c <= w2.down[i].g < s2.dr && w2.down[i].op == s2.q[w2.down[i].g - c] by {
        if i < w.down.len() {
            assert(w2.down[i] == w.down[i]);
            assert(s2.q[w.down[i].g - c] == s.q[w.down[i].g - c]);
        } else {
            assert(w2.down[i] == Msg { rev: s.er, op: o, g: s.dr });
            assert(s2.q[s.dr - c] == o);
        }
    }
    assert forall|i: int| 0 <= i < w2.down.len() implies (#[trigger] w2.down[i]).rev <= s2.er by {
        if i < w.down.len() { assert(w2.down[i] == w.down[i]); }
    }
    if w.up.len() == 0 {
        lemma_covers_push(w.down, s.er, e.rd, s.dr, Msg { rev: s.er, op: o, g: s.dr });
    }
}

pub proof fn lemma_ed_local(w: W, o: int)
    requires inv(w),
    ensures inv(ed_local(w, o)),
{
    let w2 = ed_local(w, o);
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    assert(up_ops(w2.up) =~= up_ops(w.up).push(o));
    lemma_fold_snoc(fold(s.lc, s.q.subrange(0, e.rd - c)), up_ops(w.up), o);
    assert forall|i: int| 0 <= i < w2.up.len() implies (#[trigger] w2.up[i]).rev == e.rd by {
        if i < w.up.len() { assert(w2.up[i] == w.up[i]); }
    }
}

pub proof fn lemma_srv_recv(w: W)
    requires inv(w), w.up.len() > 0,
    ensures inv(srv_recv(w)),
{
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let u = w.up[0];
    assert(u.rev == e.rd);
    let r = srv_edit(s, u.rev, u.op);
    let s2 = r.0;
    let w2 = srv_recv(w);
    let k = (e.rd - c) as int;
    let lc1 = fold(s.lc, s.q.subrange(0, k));
    let q1 = s.q.subrange(k, s.q.len() as int);
    lemma_srv_edit_wf(s, u.rev, u.op);
    lemma_tt(lc1, u.op, q1);
    let q2 = tt(u.op, q1).1;
    assert(s2.q == q2);
    assert(q2.len() == q1.len());
    assert(confirmed(s2) == e.rd);
    assert(q2.subrange(0, 0) =~= Seq::<int>::empty());
    // the editor buffer: [u0] ++ rest applied on lc1
    let ops = up_ops(w.up);
    assert(ops[0] == u.op);
    assert(up_ops(w2.up) =~= ops.drop_first());
    assert(fold(lc1, ops) == fold(ap(lc1, u.op), ops.drop_first()));
    // messages
    lemma_batch(q2, s.er + 1, u.rev);
    assert forall|i: int| 0 <= i < w2.down.len() implies (#[trigger] w2.down[i]).rev <= s2.er by {
        if i < w.down.len() { assert(w2.down[i] == w.down[i]); }
        else { assert(w2.down[i] == batch(q2, s.er + 1, u.rev)[i - w.down.len()]); }
    }
    assert forall|i: int| 0 <= i < w2.down.len() && (#[trigger] w2.down[i]).rev == s2.er
        implies confirmed(s2) <= w2.down[i].g < s2.dr && w2.down[i].op == s2.q[w2.down[i].g - confirmed(s2)] by {
        if i < w.down.len() {
            assert(w2.down[i] == w.down[i]);
            assert(w.down[i].rev <= s.er);
        } else {
            let j = i - w.down.len();
            assert(w2.down[i] == batch(q2, s.er + 1, u.rev)[j]);
        }
    }
    assert forall|i: int| 0 <= i < w2.up.len() implies (#[trigger] w2.up[i]).rev == e.rd by {
        assert(w2.up[i] == w.up[i + 1]);
    }
    if w2.up.len() == 0 {
        lemma_covers_batch(q2, s.er + 1, u.rev);
        assert forall|i: int| 0 <= i < w.down.len() implies (#[trigger] w.down[i]).rev != s2.er by {}
        lemma_covers_stale_prefix(w.down, batch(q2, s.er + 1, u.rev), s2.er, e.rd, s2.dr);
    }
}

pub proof fn lemma_ed_recv(w: W)
    requires inv(w), w.down.len() > 0,
    ensures inv(ed_recv(w)),
{
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let m = w.down[0];
    let w2 = ed_recv(w);
    assert(m.rev <= s.er);
    assert forall|i: int| 0 <= i < w2.down.len() implies (#[trigger] w2.down[i]).rev <= s.er by {
        assert(w2.down[i] == w.down[i + 1]);
    }
    assert forall|i: int| 0 <= i < w2.down.len() && (#[trigger] w2.down[i]).rev == s.er
        implies c <= w2.down[i].g < s.dr && w2.down[i].op == s.q[w2.down[i].g - c] by {
        assert(w2.down[i] == w.down[i + 1]);
    }
    if m.rev == e.re {
        // acceptance: m.rev <= er <= re == m.rev, so er == re, no edit in flight, m is non-stale
        assert(s.er == e.re);
        assert(w.up.len() == 0);
        assert(m.rev == s.er);
        assert(m.g == e.rd && e.rd < s.dr);
        assert(m.op == s.q[e.rd - c]);
        let k = (e.rd - c) as int;
        assert(s.q.subrange(0, k + 1) =~= s.q.subrange(0, k).push(s.q[k]));
        lemma_fold_snoc(s.lc, s.q.subrange(0, k), s.q[k]);
        assert(up_ops(w.up) =~= Seq::<int>::empty());
    } else {
        if w.up.len() == 0 {
            assert(s.er == e.re);
            assert(m.rev != s.er);
        }
    }
}

// ---------- results ----------
// the initial state after `Open` (OTServer::new(content), editor buffer == content)
pub proof fn lemma_init(content: Seq<char>)
    ensures inv(W {
        srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
        ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() }),
{
    let s = Srv { er: 0, dr: 0, q: Seq::<int>::empty(), lc: content, cur: content };
    assert(s.q.subrange(0, 0) =~= Seq::<int>::empty());
}

// convergence: when nothing is in flight, the editor and the daemon agree
pub proof fn theorem_quiescent_agreement(w: W)
    requires inv(w), w.up.len() == 0, w.down.len() == 0,
    ensures w.ed.buf == w.srv.cur, w.ed.rd == w.srv.dr,
{
    let s = w.srv; let e = w.ed;
    assert(covers(w.down, s.er, e.rd, s.dr));
    assert(e.rd == s.dr);
    assert(s.q.subrange(0, e.rd - confirmed(s)) =~= s.q);
    assert(up_ops(w.up) =~= Seq::<int>::empty());
}


// =====================================================================================
// Refinement of the real `OTServer` (crates/teamtype/src/ot.rs @ 6146e00).
// Bodies below are the source bodies with the syntactic rewrites listed in DESIGN.md;
// conversions and the operational-transform crate are trusted external specs.
// =====================================================================================
#[verifier::external_body]
pub struct OperationSeq { inner: () }
impl OperationSeq {
    pub uninterp spec fn view(&self) -> int;
    #[verifier::external_body]
    pub fn clone(&self) -> (r: Self) ensures r@ == self@ { unimplemented!() }
    #[verifier::external_body]
    pub fn base_len(&self) -> (r: usize) ensures r == base_len_of(self@) { unimplemented!() }
    #[verifier::external_body]
    pub fn retain(&mut self, n: u64) ensures final(self)@ == pad(old(self)@, n as nat) { unimplemented!() }
    // `.transform(..).unwrap_or_else(|_| panic!(..))`: trusted not to fail (ASSUMED)
    #[verifier::external_body]
    pub fn transform_or_panic(&self, other: &OperationSeq) -> (r: (OperationSeq, OperationSeq))
        ensures r.0@ == tr_my(self@, other@), r.1@ == tr_their(self@, other@),
    { unimplemented!() }
}

pub struct Error;
pub type Result<T> = core::result::Result<T, Error>;

#[verifier::external_body]
pub struct TextDelta { inner: () }
#[verifier::external_body]
pub struct EditorTextDelta { inner: () }
pub uninterp spec fn delta_op(d: TextDelta) -> int;     // the op a TextDelta denotes
pub uninterp spec fn ed_op(d: EditorTextDelta) -> int;  // the op an EditorTextDelta denotes
impl TextDelta {
    #[verifier::external_body]
    pub fn clone(&self) -> (r: Self) ensures r == *self { unimplemented!() }
}
// `.into()` conversions between OperationSeq and TextDelta (ASSUMED faithful)
#[verifier::external_body]
pub fn op_from_delta(d: TextDelta) -> (r: OperationSeq) ensures r@ == delta_op(d) { unimplemented!() }
#[verifier::external_body]
pub fn delta_from_op(o: OperationSeq) -> (r: TextDelta) ensures delta_op(r) == o@ { unimplemented!() }
// EditorTextDelta::try_from_delta (ASSUMED: on Ok the editor delta denotes the same op)
#[verifier::external_body]
pub fn try_from_delta(d: TextDelta, content: &str) -> (r: Result<EditorTextDelta>)
    ensures r is Ok ==> ed_op(r->Ok_0) == delta_op(d)
{ unimplemented!() }
// the `.expect(..)` variant in deltas_for_editor; trusted not to fail (ASSUMED)
#[verifier::external_body]
pub fn try_from_delta_expect(d: TextDelta, content: &str) -> (r: EditorTextDelta)
    ensures ed_op(r) == delta_op(d)
{ unimplemented!() }

pub struct RevisionedEditorTextDelta { pub revision: usize, pub delta: EditorTextDelta }
pub struct RevisionedTextDelta { pub revision: usize, pub delta: TextDelta }
// RevisionedTextDelta::try_from_rev_ed_delta (ASSUMED: on Ok the op is the editor delta's op)
#[verifier::external_body]
pub fn try_from_rev_ed_delta(r: RevisionedEditorTextDelta, content: &str) -> (o: Result<RevisionedTextDelta>)
    ensures o is Ok ==> delta_op(o->Ok_0.delta) == ed_op(r.delta) && o->Ok_0.revision == r.revision
{ unimplemented!() }

// `Vec::drain(..n)` collected
#[verifier::external_body]
pub fn drain_front(v: &mut Vec<OperationSeq>, n: usize) -> (r: Vec<OperationSeq>)
    requires n <= old(v)@.len(),
    ensures
        r@.map_values(|o: OperationSeq| o@) == old(v)@.map_values(|o: OperationSeq| o@).subrange(0, n as int),
        final(v)@.map_values(|o: OperationSeq| o@) == old(v)@.map_values(|o: OperationSeq| o@).subrange(n as int, old(v)@.len() as int),
{ unimplemented!() }

// `self.current_content.chars().count()`
#[verifier::external_body]
pub fn chars_count(s: &String) -> (r: usize) ensures r == s@.len() { unimplemented!() }

// source `force_apply`; its body uses the library `apply`, trusted not to panic (ASSUMED)
#[verifier::external_body]
fn force_apply(document: &str, op_seq: OperationSeq) -> (r: String)
    ensures r@ == ap(document@, op_seq@),
{ unimplemented!() }

pub open spec fn ops(v: Seq<OperationSeq>) -> Seq<int> { v.map_values(|o: OperationSeq| o@) }

// corr: crates/teamtype/src/ot.rs :: transform_through_operations
fn transform_through_operations(
    their_op_seq: OperationSeq,
    my_operations: &Vec<OperationSeq>,
) -> (r: (OperationSeq, Vec<OperationSeq>))
    ensures
        r.0@ == tt(their_op_seq@, ops(my_operations@)).0,
        ops(r.1@) == tt(their_op_seq@, ops(my_operations@)).1,
{
    let ghost t0 = their_op_seq@;
    let ghost my = ops(my_operations@);
    let mut their_op_seq = their_op_seq;
    let mut transformed_my_operations: Vec<OperationSeq> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(my.subrange(0, my.len() as int) =~= my);
        assert(ops(transformed_my_operations@) =~= Seq::<int>::empty());
        assert(Seq::<int>::empty().add(tt(t0, my).1) =~= tt(t0, my).1);
    }
    while i < my_operations.len()
        invariant
            i <= my_operations@.len(),
            my == ops(my_operations@),
            transformed_my_operations@.len() == i,
            // the recursion `tt` unrolled i steps
            tt(t0, my).0 == tt(their_op_seq@, my.subrange(i as int, my.len() as int)).0,
            tt(t0, my).1 == ops(transformed_my_operations@).add(tt(their_op_seq@, my.subrange(i as int, my.len() as int)).1),
        decreases my_operations@.len() - i,
    {
        let mut my_op_seq = my_operations[i].clone();
        let ghost m_orig = my_op_seq@;
        let ghost t_orig = their_op_seq@;
        if my_op_seq.base_len() < their_op_seq.base_len() {
            let diff = their_op_seq.base_len() - my_op_seq.base_len();
            my_op_seq.retain(diff as u64);
        } else {
            let diff = my_op_seq.base_len() - their_op_seq.base_len();
            their_op_seq.retain(diff as u64);
        }
        assert(my_op_seq@ == fix_m(m_orig, t_orig));
        assert(their_op_seq@ == fix_t(m_orig, t_orig));
        let (my_prime, their_prime) = my_op_seq.transform_or_panic(&their_op_seq);
        let ghost prev = ops(transformed_my_operations@);
        let ghost rest_before = my.subrange(i as int, my.len() as int);
        transformed_my_operations.push(my_prime);
        their_op_seq = their_prime;
        proof {
            assert(rest_before[0] == m_orig);
            assert(rest_before.drop_first() =~= my.subrange(i as int + 1, my.len() as int));
            assert(ops(transformed_my_operations@) =~= prev.push(my_prime@));
            let r = tt(their_prime@, my.subrange(i as int + 1, my.len() as int));
            assert(tt(t_orig, rest_before) == (r.0, seq![tr_my(fix_m(m_orig, t_orig), fix_t(m_orig, t_orig))].add(r.1)));
            assert(prev.push(my_prime@).add(r.1) =~= prev.add(seq![my_prime@].add(r.1)));
        }
        i += 1;
    }
    proof {
        assert(my.subrange(i as int, my.len() as int) =~= Seq::<int>::empty());
        assert(ops(transformed_my_operations@).add(Seq::empty()) =~= ops(transformed_my_operations@));
    }
    (their_op_seq, transformed_my_operations)
}
// corr-end

pub struct OTServer {
    pub editor_revision: usize,
    pub daemon_revision: usize,
    pub operations: Vec<OperationSeq>,
    pub editor_queue: Vec<OperationSeq>,
    pub current_content: String,
    pub last_confirmed_editor_content: String,
}

impl OTServer {
    // the ghost state the protocol model reasons about
    pub open spec fn view(&self) -> Srv {
        Srv {
            er: self.editor_revision as nat,
            dr: self.daemon_revision as nat,
            q: ops(self.editor_queue@),
            lc: self.last_confirmed_editor_content@,
            cur: self.current_content@,
        }
    }

    // corr: crates/teamtype/src/ot.rs :: OTServer::new
    pub fn new(initial_content: String) -> (r: Self)
        ensures wf(r@), r@.er == 0, r@.dr == 0, r@.cur == initial_content@, r@.lc == initial_content@, r@.q.len() == 0,
    {
        Self {
            last_confirmed_editor_content: initial_content.clone(),
            current_content: initial_content,
            editor_revision: 0, daemon_revision: 0,
            operations: Vec::new(), editor_queue: Vec::new(),
        }
    }
    // corr-end

    // ot.rs `apply_crdt_change`
    // corr: crates/teamtype/src/ot.rs :: OTServer::apply_crdt_change
    pub fn apply_crdt_change(&mut self, delta: &TextDelta) -> (r: Result<RevisionedEditorTextDelta>)
        requires wf(old(self)@), old(self).daemon_revision < usize::MAX,
        ensures
            // a rejected change leaves the state untouched
            r is Err ==> final(self)@ == old(self)@,
            // an accepted one is exactly the model's `srv_crdt`, and sends the model's message
            r is Ok ==> {
                &&& final(self)@ == srv_crdt(old(self)@, delta_op(*delta)).0
                &&& r->Ok_0.revision == srv_crdt(old(self)@, delta_op(*delta)).1.rev
                &&& ed_op(r->Ok_0.delta) == srv_crdt(old(self)@, delta_op(*delta)).1.op
                &&& wf(final(self)@)
            },
    {
        // Validate before mutating, so that a rejected change leaves the state untouched.
        let op_seq: OperationSeq = op_from_delta(delta.clone());
        if op_seq.base_len() > chars_count(&self.current_content) {
            return Err(Error); // bail!
        }
        // Use "previous" content to transform into editor text delta.
        let editor_delta = match try_from_delta(delta.clone(), self.current_content.as_str()) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };

        // We can apply the change immediately.
        self.operations.push(op_seq.clone());
        self.editor_queue.push(op_seq.clone());
        self.daemon_revision += 1;
        self.current_content = force_apply(self.current_content.as_str(), op_seq);
        proof {
            assert(ops(self.editor_queue@) =~= ops(old(self).editor_queue@).push(delta_op(*delta)));
            lemma_srv_crdt_wf(old(self)@, delta_op(*delta));
        }

        // We assume that the editor is up-to-date, and send the operation to it.
        // If it can't accept it, we will transform and send it later.
        Ok(RevisionedEditorTextDelta {
            revision: self.editor_revision,
            delta: editor_delta,
        })
    }
    // corr-end

    // ot.rs `apply_editor_operation`
    // corr: crates/teamtype/src/ot.rs :: OTServer::apply_editor_operation
    pub fn apply_editor_operation(
        &mut self,
        rev_editor_delta: RevisionedEditorTextDelta,
    ) -> (r: Result<(TextDelta, Vec<RevisionedEditorTextDelta>)>)
        requires wf(old(self)@), old(self).editor_revision < usize::MAX,
        ensures
            // no panic, no overflow; revisions: editor_revision counts every call, even rejected ones
            final(self).editor_revision == old(self).editor_revision + 1,
            final(self).daemon_revision == old(self).daemon_revision,
            // no error path breaks the server invariant
            wf(final(self)@),
            // a rejected edit never changes the daemon text
            r is Err ==> final(self).current_content@ == old(self).current_content@,
            // an accepted edit is exactly the model's `srv_edit` with the editor's op,
            // and returns the transformed op for the CRDT and the model's batch for the editor
            r is Ok ==> {
                &&& confirmed(old(self)@) <= rev_editor_delta.revision <= old(self).daemon_revision
                &&& final(self)@ == srv_edit(old(self)@, rev_editor_delta.revision as nat, ed_op(rev_editor_delta.delta)).0
                &&& delta_op(r->Ok_0.0) == tt(ed_op(rev_editor_delta.delta),
                        old(self).editor_queue@.map_values(|o: OperationSeq| o@).subrange(
                            rev_editor_delta.revision - confirmed(old(self)@), old(self).editor_queue@.len() as int)).0
                &&& r->Ok_0.1@.len() == final(self).editor_queue@.len()
                &&& forall|i: int| 0 <= i < r->Ok_0.1@.len() ==>
                        (#[trigger] r->Ok_0.1@[i]).revision == final(self).editor_revision
                        && ed_op(r->Ok_0.1@[i].delta) == final(self)@.q[i]
            },
    {
        let daemon_revision = rev_editor_delta.revision;
        self.editor_revision += 1;

        let mut op_seq: OperationSeq;

        if daemon_revision > self.daemon_revision {
            proof { lemma_wf_er_only(old(self)@, self@); }
            return Err(Error); // bail!
        }

        // The operation might apply to an older daemon revision.
        // We need to transform it through the daemon operations that have happened since then.

        // But we at least we know that the editor has seen all daemon operations until
        // daemon_revision. So we can remove them from the editor queue.
        let daemon_operations_to_transform = self.daemon_revision - daemon_revision;
        if self.editor_queue.len() < daemon_operations_to_transform {
            proof { lemma_wf_er_only(old(self)@, self@); }
            return Err(Error); // bail!
        }
        let seen_operations = self.editor_queue.len() - daemon_operations_to_transform;
        let ghost q0 = ops(self.editor_queue@);
        let ghost l0 = self.last_confirmed_editor_content@;
        let confirmed_queue = drain_front(&mut self.editor_queue, seen_operations);
        assert(ops(confirmed_queue@) == q0.subrange(0, seen_operations as int));
        let mut i: usize = 0;
        while i < confirmed_queue.len()
            invariant
                i <= confirmed_queue@.len(),
                seen_operations <= q0.len(),
                confirmed_queue@.len() == seen_operations,
                ops(confirmed_queue@) == q0.subrange(0, seen_operations as int),
                self.last_confirmed_editor_content@ == fold(l0, q0.subrange(0, i as int)),
            decreases confirmed_queue@.len() - i,
        {
            let confirmed_editor_op = &confirmed_queue[i];
            proof {
                assert(q0.subrange(0, i + 1) =~= q0.subrange(0, i as int).push(ops(confirmed_queue@)[i as int]));
                lemma_fold_snoc(l0, q0.subrange(0, i as int), ops(confirmed_queue@)[i as int]);
            }
            self.last_confirmed_editor_content = force_apply(
                self.last_confirmed_editor_content.as_str(),
                confirmed_editor_op.clone(),
            );
            i += 1;
        }
        proof { lemma_fold_split(l0, q0, seen_operations as int); }
        let rev_delta = match try_from_rev_ed_delta(
            rev_editor_delta,
            self.last_confirmed_editor_content.as_str(),
        ) {
            Ok(x) => x,
            Err(e) => {
                // the queue was drained and the confirmed text advanced: still consistent
                proof {
                    assert(ops(self.editor_queue@) =~= q0.subrange(seen_operations as int, q0.len() as int));
                    lemma_wf_after_confirm(old(self)@, seen_operations as int, self@);
                }
                return Err(e)
            },
        };
        op_seq = op_from_delta(rev_delta.delta);

        let ghost l1 = self.last_confirmed_editor_content@;
        let ghost e = op_seq@;
        self.last_confirmed_editor_content =
            force_apply(self.last_confirmed_editor_content.as_str(), op_seq.clone());
        let (op_seq2, q2) = transform_through_operations(op_seq, &self.editor_queue);
        proof {
            assert(ops(self.editor_queue@) =~= q0.subrange(seen_operations as int, q0.len() as int));
        }
        op_seq = op_seq2;
        self.editor_queue = q2;
        self.operations.push(op_seq.clone());
        self.current_content = force_apply(self.current_content.as_str(), op_seq.clone());

        let deltas_for_editor = self.deltas_for_editor();
        proof {
            let s0 = old(self)@;
            let k = seen_operations as int;
            assert(k == (rev_editor_delta.revision - confirmed(s0)) as int);
            lemma_srv_edit_wf(s0, rev_editor_delta.revision as nat, e);
            assert(self@ == srv_edit(s0, rev_editor_delta.revision as nat, e).0);
        }

        Ok((delta_from_op(op_seq), deltas_for_editor))
    }
    // corr-end

    // ot.rs `deltas_for_editor`
    // corr: crates/teamtype/src/ot.rs :: OTServer::deltas_for_editor
    fn deltas_for_editor(&self) -> (r: Vec<RevisionedEditorTextDelta>)
        ensures
            r@.len() == self.editor_queue@.len(),
            forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]).revision == self.editor_revision
                && ed_op(r@[i].delta) == ops(self.editor_queue@)[i],
    {
        let mut to_editor: Vec<RevisionedEditorTextDelta> = Vec::new();
        let mut document = self.last_confirmed_editor_content.clone();
        let mut i: usize = 0;
        while i < self.editor_queue.len()
            invariant
                i <= self.editor_queue@.len(),
                to_editor@.len() == i,
                forall|j: int| 0 <= j < i ==> (#[trigger] to_editor@[j]).revision == self.editor_revision
                    && ed_op(to_editor@[j].delta) == ops(self.editor_queue@)[j],
            decreases self.editor_queue@.len() - i,
        {
            let editor_op = &self.editor_queue[i];
            let delta: TextDelta = delta_from_op(editor_op.clone());
            let ed_delta = try_from_delta_expect(delta, document.as_str());
            to_editor.push(RevisionedEditorTextDelta {
                revision: self.editor_revision,
                delta: ed_delta,
            });
            document = force_apply(document.as_str(), editor_op.clone());
            i += 1;
        }
        to_editor
    // corr-end
    }
}

// error paths keep the server invariant
pub proof fn lemma_wf_er_only(s0: Srv, s1: Srv)
    requires wf(s0), s1.dr == s0.dr, s1.q == s0.q, s1.lc == s0.lc, s1.cur == s0.cur,
    ensures wf(s1),
{}

pub proof fn lemma_wf_after_confirm(s0: Srv, k: int, s1: Srv)
    requires wf(s0), 0 <= k <= s0.q.len(), s1.dr == s0.dr,
        s1.q == s0.q.subrange(k, s0.q.len() as int), s1.lc == fold(s0.lc, s0.q.subrange(0, k)), s1.cur == s0.cur,
    ensures wf(s1),
{
    lemma_fold_split(s0.lc, s0.q, k);
}



// Non-vacuity: a concrete run in which a daemon message is overtaken by an editor edit, ignored by
// the editor, retransmitted in transformed form, and applied. It ends quiescent, so
// `theorem_quiescent_agreement` is not about an unreachable state.
pub proof fn example_run(content: Seq<char>, o1: int, o2: int)
    ensures ({
        let w0 = W { srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
                     ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() };
        let w1 = crdt_step(w0, o1);      // daemon op o1 sent with revision 0
        let w2 = ed_local(w1, o2);       // editor types o2 before seeing o1
        let w3 = srv_recv(w2);           // daemon transforms o2 through o1, resends o1' with revision 1
        let w4 = ed_recv(w3);            // o1 (revision 0) is ignored: the editor already sent an edit
        let w5 = ed_recv(w4);            // o1' (revision 1) is applied
        &&& inv(w5) && w5.up.len() == 0 && w5.down.len() == 0
        &&& w1.down.len() == 1 && w2.up.len() == 1 && w3.down.len() == 2
        &&& w4.ed.rd == 0 && w5.ed.rd == 1
        &&& w5.ed.buf == w5.srv.cur
    }),
{
    lemma_init(content);
    let w0 = W { srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
                 ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() };
    lemma_crdt_step(w0, o1);
    let w1 = crdt_step(w0, o1);
    lemma_ed_local(w1, o2);
    let w2 = ed_local(w1, o2);
    lemma_srv_recv(w2);
    let w3 = srv_recv(w2);
    lemma_ed_recv(w3);
    let w4 = ed_recv(w3);
    lemma_ed_recv(w4);
    let w5 = ed_recv(w4);
    // unfold the concrete queues
    assert(w1.srv.q =~= seq![o1]);
    assert(w2.up[0] == Up { rev: 0, op: o2 });
    let k = (0 - confirmed(w2.srv)) as int;
    assert(w2.srv.q.subrange(0, 0) =~= Seq::<int>::empty());
    assert(w2.srv.q.subrange(0, w2.srv.q.len() as int) =~= w2.srv.q);
    lemma_batch(tt(o2, w2.srv.q).1, 1, 0);
    assert(w3.down.len() == 2);
    assert(w4.ed.rd == 0);
    assert(w3.down[1].rev == 1);
    assert(w5.ed.rd == 1);
    assert(w4.down.len() == 1);
    assert(w5.down.len() == 0);
    theorem_quiescent_agreement(w5);
}

} // verus!
}
mod bnd {
// (authored by agents) Verus model of document.rs cache maintenance (receive_sync_message_log_patches)
use vstd::prelude::*;
verus! {

pub type Path = nat;
pub enum Entry { Text(Seq<int>), Bytes(Seq<int>) }
pub type View = Map<Path, Entry>;

pub open spec fn get(m: View, p: Path) -> Option<Entry> {
    if m.dom().contains(p) { Some(m[p]) } else { None }
}
pub open spec fn is_txt(m: View, p: Path) -> bool {
    m.dom().contains(p) && m[p] is Text
}
/// text of p, "" if p is absent or bytes (what the cache code does for FileChange on a missing/bytes entry)
pub open spec fn txt(m: View, p: Path) -> Seq<int> {
    if is_txt(m, p) { m[p]->Text_0 } else { Seq::empty() }
}
pub open spec fn rep(t: Seq<int>, i: int, n: int, s: Seq<int>) -> Seq<int> {
    t.subrange(0, i) + s + t.subrange(i + n, t.len() as int)
}
pub open spec fn rep_ok(t: Seq<int>, i: int, n: int) -> bool {
    0 <= i && 0 <= n && i + n <= t.len()
}

/// Abstract Automerge patch, already in the shape types.rs accepts
/// (PutText = PutMap(Text) incl. the replaced_text_objects_as_puts rewrite; Conflict = Conflict).
pub enum Patch {
    PutText(Path),
    PutBytes(Path, Seq<int>),
    Delete(Path),
    Splice(Path, int, Seq<int>),
    DelSeq(Path, int, int),
    Conflict(Path),
}

/// ASSUMED semantics of a patch (Automerge patch log replayed on the previous visible state).
pub open spec fn step_view(v: View, pt: Patch) -> Option<View> {
    match pt {
        Patch::PutText(p) => Some(v.insert(p, Entry::Text(Seq::empty()))),
        Patch::PutBytes(p, b) => Some(v.insert(p, Entry::Bytes(b))),
        Patch::Delete(p) => Some(v.remove(p)),
        Patch::Splice(p, i, s) =>
            if is_txt(v, p) && rep_ok(txt(v, p), i, 0) {
                Some(v.insert(p, Entry::Text(rep(txt(v, p), i, 0, s))))
            } else { None },
        Patch::DelSeq(p, i, n) =>
            if is_txt(v, p) && rep_ok(txt(v, p), i, n) {
                Some(v.insert(p, Entry::Text(rep(txt(v, p), i, n, Seq::empty()))))
            } else { None },
        Patch::Conflict(_) => Some(v),
    }
}

pub open spec fn replay(v: View, ps: Seq<Patch>) -> Option<View>
    decreases ps.len(),
{
    if ps.len() == 0 { Some(v) } else {
        match step_view(v, ps[0]) {
            Some(v1) => replay(v1, ps.drop_first()),
            None => None,
        }
    }
}

/// Cache update performed by the Rust code for one effect; `f` is the document AFTER the whole
/// message (the code consults text_obj(path) on the final document for FileRemoval).
pub open spec fn gfin(f: View, p: Path) -> Option<Entry> {
    if is_txt(f, p) { Some(Entry::Text(Seq::empty())) } else { None }
}
pub open spec fn cache_set(c: View, p: Path, o: Option<Entry>) -> View {
    match o { Some(e) => c.insert(p, e), None => c.remove(p) }
}
pub open spec fn cache_step(c: View, f: View, pt: Patch) -> View {
    match pt {
        Patch::PutText(p) => cache_set(c, p, gfin(f, p)),
        Patch::Delete(p) => cache_set(c, p, gfin(f, p)),
        Patch::PutBytes(p, b) => c.insert(p, Entry::Bytes(b)),
        Patch::Splice(p, i, s) => c.insert(p, Entry::Text(rep(txt(c, p), i, 0, s))),
        Patch::DelSeq(p, i, n) => c.insert(p, Entry::Text(rep(txt(c, p), i, n, Seq::empty()))),
        Patch::Conflict(_) => c,
    }
}
/// The delta applied to the cache text must fit (else the Rust code panics).
pub open spec fn cache_fits(c: View, pt: Patch) -> bool {
    match pt {
        Patch::Splice(p, i, _) => rep_ok(txt(c, p), i, 0),
        Patch::DelSeq(p, i, n) => rep_ok(txt(c, p), i, n),
        _ => true,
    }
}

pub open spec fn rel_at(c: View, v: View, f: View, p: Path) -> bool {
    get(c, p) == get(v, p)
    || (get(c, p) == gfin(f, p)
        && (get(v, p) is None || get(v, p) == Some(Entry::Text(Seq::<int>::empty()))))
}
pub open spec fn rel(c: View, v: View, f: View) -> bool {
    forall|p: Path| #[trigger] rel_at(c, v, f, p)
}

pub proof fn step_preserves(c: View, v: View, f: View, pt: Patch)
    requires rel(c, v, f), step_view(v, pt) is Some,
    ensures
        cache_fits(c, pt),
        rel(cache_step(c, f, pt), step_view(v, pt)->Some_0, f),
{
    let v1 = step_view(v, pt)->Some_0;
    let c1 = cache_step(c, f, pt);
    // the text of c at the touched path equals that of v (both absent/empty or equal)
    match pt {
        Patch::Splice(p, _, _) | Patch::DelSeq(p, _, _) => {
            assert(rel_at(c, v, f, p));
            assert(txt(c, p) == txt(v, p));
        }
        _ => {}
    }
    assert forall|q: Path| #[trigger] rel_at(c1, v1, f, q) by {
        assert(rel_at(c, v, f, q));
        match pt {
            Patch::PutText(p) | Patch::Delete(p) => {
                if q == p {
                    if is_txt(f, p) { assert(get(c1, q) == get(v1, q) || true); }
                }
            }
            Patch::Splice(p, i, s) => {
                if q == p { assert(get(c1, q) == get(v1, q)); }
            }
            Patch::DelSeq(p, i, n) => {
                if q == p { assert(get(c1, q) == get(v1, q)); }
            }
            _ => {}
        }
    }
}

/// Final theorem: if the cache starts equal to the document, then after the cache is updated with
/// every effect of a message whose patches replay to f, the cache equals f.
pub proof fn replay_preserves(c: View, v: View, f: View, ps: Seq<Patch>)
    requires rel(c, v, f), replay(v, ps) == Some(f),
    ensures forall|p: Path| #[trigger] get(fold_cache(c, f, ps), p) == get(f, p),
    decreases ps.len(),
{
    if ps.len() == 0 {
        assert forall|p: Path| #[trigger] get(c, p) == get(f, p) by {
            assert(rel_at(c, f, f, p));
        }
    } else {
        let v1 = step_view(v, ps[0])->Some_0;
        step_preserves(c, v, f, ps[0]);
        replay_preserves(cache_step(c, f, ps[0]), v1, f, ps.drop_first());
    }
}

pub open spec fn fold_cache(c: View, f: View, ps: Seq<Patch>) -> View
    decreases ps.len(),
{
    if ps.len() == 0 { c } else { fold_cache(cache_step(c, f, ps[0]), f, ps.drop_first()) }
}

// ======================= daemon.rs: ReceiveSyncMessage handling =======================

pub struct Rep { pub i: int, pub n: int, pub s: Seq<int> }
pub open spec fn app(t: Seq<int>, r: Rep) -> Seq<int> { rep(t, r.i, r.n, r.s) }
pub open spec fn app_all(t: Seq<int>, ds: Seq<Rep>) -> Seq<int>
    decreases ds.len(),
{
    if ds.len() == 0 { t } else { app(app_all(t, ds.drop_last()), ds.last()) }
}
pub open spec fn app_ok(t: Seq<int>, ds: Seq<Rep>) -> bool
    decreases ds.len(),
{
    if ds.len() == 0 { true } else {
        app_ok(t, ds.drop_last())
            && rep_ok(app_all(t, ds.drop_last()), ds.last().i, ds.last().n)
    }
}
proof fn app_push(t: Seq<int>, ds: Seq<Rep>, r: Rep)
    ensures
        app_all(t, ds.push(r)) == app(app_all(t, ds), r),
        app_ok(t, ds.push(r)) == (app_ok(t, ds) && rep_ok(app_all(t, ds), r.i, r.n)),
{
    assert(ds.push(r).drop_last() =~= ds);
}

/// Daemon state touched while handling one ReceiveSyncMessage.
/// `own` holds (editor, path) pairs: the editor has the file open (OTServer present).
pub struct D {
    pub cache: View,           // Document.files == the CRDT (revival keeps them equal)
    pub view: View,            // ghost: CRDT state after the patches processed so far
    pub own: Set<(nat, nat)>,
    pub deltas: Map<Path, Seq<Rep>>, // file_deltas, grouped per path (editors treat paths independently)
    pub disk: View,
    pub pend: Set<Path>,       // paths in file_deltas (written after the loop)
    pub done: Set<Path>,       // ghost: paths touched so far
}

/// Constants of one message: excluded paths, buffers at the start, CRDT before and after.
pub struct K { pub excl: spec_fn(Path) -> bool, pub buf0: Map<(nat, nat), Seq<int>>, pub c0: View, pub f: View }

pub open spec fn owned_any(own: Set<(nat, nat)>, p: Path) -> bool {
    exists|e: nat| #[trigger] own.contains((e, p))
}
pub open spec fn inval(own: Set<(nat, nat)>, p: Path) -> Set<(nat, nat)> {
    own.filter(|k: (nat, nat)| k.1 != p)
}
pub open spec fn dl(d: D, p: Path) -> Seq<Rep> {
    if d.deltas.dom().contains(p) { d.deltas[p] } else { Seq::empty() }
}
/// write_file when git is not running: writes the cache text/bytes, does nothing if the cache lacks the path.
pub open spec fn wr(disk: View, cache: View, p: Path) -> View {
    if cache.dom().contains(p) { disk.insert(p, cache[p]) } else { disk }
}

/// One effect of the `for patch_effect in patch_effects` loop in daemon.rs (git not running).
pub open spec fn dstep(k: K, d: D, pt: Patch) -> D {
    let v1 = step_view(d.view, pt)->Some_0;
    match pt {
        Patch::Splice(p, i, s) => D {
            view: v1,
            deltas: d.deltas.insert(p, dl(d, p).push(Rep { i, n: 0, s })),
            pend: d.pend.insert(p), done: d.done.insert(p), ..d },
        Patch::DelSeq(p, i, n) => D {
            view: v1,
            deltas: d.deltas.insert(p, dl(d, p).push(Rep { i, n, s: Seq::empty() })),
            pend: d.pend.insert(p), done: d.done.insert(p), ..d },
        Patch::PutBytes(p, _) => D {
            view: v1, own: inval(d.own, p),
            disk: if (k.excl)(p) { d.disk } else { wr(d.disk, d.cache, p) },
            done: d.done.insert(p), ..d },
        Patch::Conflict(_) => D { view: v1, ..d },
        Patch::PutText(p) | Patch::Delete(p) =>
            if (k.excl)(p) { D { view: v1, done: d.done.insert(p), ..d } }
            else if !owned_any(d.own, p) {
                if d.cache.dom().contains(p) {
                    D { view: v1, disk: wr(d.disk, d.cache, p), done: d.done.insert(p), ..d }
                } else {
                    D { view: v1, disk: d.disk.remove(p), done: d.done.insert(p), ..d }
                }
            } else {
                // editor owns it: replace earlier deltas by "delete all previous content", bring back empty file
                let before = txt(k.c0, p).len() as int;
                D { view: v1,
                    deltas: d.deltas.insert(p, seq![Rep { i: 0, n: before, s: Seq::empty() }]),
                    cache: if d.cache.dom().contains(p) { d.cache }
                           else { d.cache.insert(p, Entry::Text(Seq::empty())) },
                    pend: d.pend.insert(p), done: d.done.insert(p), ..d }
            },
    }
}

pub open spec fn fin_dom(k: K, d: D) -> Set<Path> {
    d.disk.dom().union(d.pend.intersect(d.cache.dom()).filter(|p: Path| !(k.excl)(p)))
}
pub open spec fn fin_write(k: K, d: D) -> View {
    Map::new(
        fin_dom(k, d),
        |p: Path| if d.pend.contains(p) && d.cache.dom().contains(p) && !(k.excl)(p) { d.cache[p] }
                  else { d.disk[p] },
    )
}

pub open spec fn inv_cache(k: K, d: D) -> bool {
    forall|p: Path| #![trigger get(d.cache, p)]
        get(d.cache, p) == get(k.f, p)
        || (get(k.f, p) is None && get(d.cache, p) == Some(Entry::Text(Seq::<int>::empty())))
}
pub open spec fn inv_buf(k: K, d: D) -> bool {
    forall|e: nat, p: Path| #[trigger] d.own.contains((e, p)) ==> {
        &&& k.buf0.dom().contains((e, p))
        &&& is_txt(k.c0, p) && k.buf0[(e, p)] == txt(k.c0, p)
        &&& !(k.excl)(p)
        &&& app_ok(k.buf0[(e, p)], dl(d, p))
        &&& app_all(k.buf0[(e, p)], dl(d, p)) == txt(d.view, p)
    }
}
pub open spec fn inv_m(k: K, d: D) -> bool {
    forall|p: Path| #[trigger] owned_any(d.own, p) ==> {
        &&& (is_txt(d.view, p) || get(d.view, p) is None)
        &&& (get(d.view, p) is None ==>
                get(d.cache, p) == Some(Entry::Text(Seq::<int>::empty())) || get(k.f, p) is Some)
    }
}
pub open spec fn inv_disk(k: K, d: D) -> bool {
    forall|p: Path| #![trigger get(d.disk, p)]
        (!owned_any(d.own, p) && !(k.excl)(p)) ==> {
            if !d.done.contains(p) {
                get(d.disk, p) == get(k.c0, p)
            } else {
                get(d.disk, p) == get(d.cache, p)
                || (d.pend.contains(p) && d.cache.dom().contains(p))
                || (!d.cache.dom().contains(p) && get(d.view, p) is Some)
            }
        }
}
pub open spec fn inv_misc(k: K, d: D) -> bool {
    &&& forall|p: Path| #![trigger get(d.view, p)] !d.done.contains(p) ==> get(d.view, p) == get(k.c0, p)
    &&& forall|p: Path| #![trigger get(d.cache, p)] get(d.cache, p) != get(k.f, p) ==> d.done.contains(p)
    &&& forall|p: Path| #[trigger] d.pend.contains(p) ==> d.done.contains(p)
}
pub open spec fn inv(k: K, d: D) -> bool {
    inv_cache(k, d) && inv_buf(k, d) && inv_m(k, d) && inv_disk(k, d) && inv_misc(k, d)
}

pub open spec fn tpath(pt: Patch) -> Path {
    match pt {
        Patch::Splice(p, _, _) | Patch::DelSeq(p, _, _) | Patch::PutBytes(p, _)
        | Patch::PutText(p) | Patch::Delete(p) | Patch::Conflict(p) => p,
    }
}
proof fn dstep_done(k: K, d: D, pt: Patch)
    requires step_view(d.view, pt) is Some,
    ensures
        dstep(k, d, pt).done == (if pt is Conflict { d.done } else { d.done.insert(tpath(pt)) }),
        dstep(k, d, pt).view == step_view(d.view, pt)->Some_0,
{
    match pt {
        Patch::PutText(p) | Patch::Delete(p) => {
            if (k.excl)(p) {} else if !owned_any(d.own, p) {
                if d.cache.dom().contains(p) {} else {}
            } else {}
        }
        _ => {}
    }
}

proof fn fin_get(k: K, d: D, p: Path)
    ensures get(fin_write(k, d), p) ==
        (if d.pend.contains(p) && d.cache.dom().contains(p) && !(k.excl)(p) { Some(d.cache[p]) }
         else { get(d.disk, p) }),
{
    let fw = fin_write(k, d);
    if d.pend.contains(p) && d.cache.dom().contains(p) && !(k.excl)(p) {
        assert(fin_dom(k, d).contains(p));
    } else {
        assert(fin_dom(k, d).contains(p) == d.disk.dom().contains(p));
    }
}

proof fn inval_props(own: Set<(nat, nat)>, p: Path)
    ensures
        forall|e: nat, q: Path| #[trigger] inval(own, p).contains((e, q)) <==> (own.contains((e, q)) && q != p),
        forall|q: Path| #[trigger] owned_any(inval(own, p), q) <==> (q != p && owned_any(own, q)),
{
    assert forall|q: Path| #[trigger] owned_any(inval(own, p), q) <==> (q != p && owned_any(own, q)) by {
        if owned_any(inval(own, p), q) {
            let e = choose|e: nat| inval(own, p).contains((e, q));
            assert(own.contains((e, q)));
        }
        if q != p && owned_any(own, q) {
            let e = choose|e: nat| own.contains((e, q));
            assert(inval(own, p).contains((e, q)));
        }
    }
}

pub proof fn dstep_preserves(k: K, d: D, pt: Patch)
    requires inv(k, d), step_view(d.view, pt) is Some,
    ensures inv_cache(k, dstep(k, d, pt)), inv_buf(k, dstep(k, d, pt)), inv_m(k, dstep(k, d, pt)), inv_disk(k, dstep(k, d, pt)), inv_misc(k, dstep(k, d, pt)),
{
    let d1 = dstep(k, d, pt);
    dstep_done(k, d, pt);
    inval_props(d.own, match pt { Patch::PutBytes(p, _) => p, _ => 0 });
    match pt {
        Patch::Splice(p, i, s) => {
            let r = Rep { i, n: 0, s };
            assert forall|e: nat, q: Path| #[trigger] d1.own.contains((e, q)) implies {
                &&& k.buf0.dom().contains((e, q))
                &&& is_txt(k.c0, q) && k.buf0[(e, q)] == txt(k.c0, q)
                &&& !(k.excl)(q)
                &&& app_ok(k.buf0[(e, q)], dl(d1, q))
                &&& app_all(k.buf0[(e, q)], dl(d1, q)) == txt(d1.view, q)
            } by {
                if q == p { app_push(k.buf0[(e, q)], dl(d, p), r); }
            }
        }
        Patch::DelSeq(p, i, n) => {
            let r = Rep { i, n, s: Seq::empty() };
            assert forall|e: nat, q: Path| #[trigger] d1.own.contains((e, q)) implies {
                &&& k.buf0.dom().contains((e, q))
                &&& is_txt(k.c0, q) && k.buf0[(e, q)] == txt(k.c0, q)
                &&& !(k.excl)(q)
                &&& app_ok(k.buf0[(e, q)], dl(d1, q))
                &&& app_all(k.buf0[(e, q)], dl(d1, q)) == txt(d1.view, q)
            } by {
                if q == p { app_push(k.buf0[(e, q)], dl(d, p), r); }
            }
        }
        Patch::PutText(p) | Patch::Delete(p) => {
            if !(k.excl)(p) && owned_any(d.own, p) {
                let e = choose|e: nat| d.own.contains((e, p));
                assert(k.buf0[(e, p)] == txt(k.c0, p));
                let before = txt(k.c0, p).len() as int;
                let r = Rep { i: 0, n: before, s: Seq::empty() };
                let ds = seq![r];
                assert(ds.drop_last() =~= Seq::<Rep>::empty());
                assert(ds.last() == r);
                assert(app_all(k.buf0[(e, p)], Seq::<Rep>::empty()) == k.buf0[(e, p)]);
                assert(app_ok(k.buf0[(e, p)], Seq::<Rep>::empty()));
                assert(app_ok(k.buf0[(e, p)], ds));
                assert(app_all(k.buf0[(e, p)], ds) =~= Seq::<int>::empty());
                assert(txt(k.c0, p).subrange(0, 0) + Seq::<int>::empty() + txt(k.c0, p).subrange(before, before) =~= Seq::<int>::empty());
            }
        }
        _ => {}
    }
    assert forall|q: Path| #![trigger get(d1.cache, q)]
        get(d1.cache, q) == get(k.f, q)
        || (get(k.f, q) is None && get(d1.cache, q) == Some(Entry::Text(Seq::<int>::empty()))) by {
        assert(get(d.cache, q) == get(k.f, q)
            || (get(k.f, q) is None && get(d.cache, q) == Some(Entry::Text(Seq::<int>::empty()))));
    }
    assert forall|q: Path| #![trigger get(d1.view, q)] !d1.done.contains(q) implies get(d1.view, q) == get(k.c0, q) by {
        assert(!d.done.contains(q));
        if !(pt is Conflict) { assert(q != tpath(pt)); }
        assert(get(step_view(d.view, pt)->Some_0, q) == get(d.view, q));
    }
    assert forall|q: Path| #![trigger get(d1.cache, q)] get(d1.cache, q) != get(k.f, q) implies d1.done.contains(q) by {
        if !d.done.contains(q) { assert(get(d.cache, q) == get(k.f, q)); }
    }
    assert forall|q: Path| #[trigger] d1.pend.contains(q) implies d1.done.contains(q) by {
        if d.pend.contains(q) { assert(d.done.contains(q)); }
    }
}

pub open spec fn fold_d(k: K, d: D, ps: Seq<Patch>) -> D
    decreases ps.len(),
{
    if ps.len() == 0 { d } else {
        fold_d(k, dstep(k, d, ps[0]), ps.drop_first())
    }
}

/// State right after Document::receive_sync_message_log_patches: cache == f.
pub open spec fn init_d(k: K, own0: Set<(nat, nat)>, disk0: View) -> D {
    D { cache: k.f, view: k.c0, own: own0, deltas: Map::empty(), disk: disk0,
        pend: Set::empty(), done: Set::empty() }
}
/// Assumptions on the state before the message (invariants of the daemon between messages).
pub open spec fn pre(k: K, own0: Set<(nat, nat)>, disk0: View) -> bool {
    // an editor that owns a file holds exactly the daemon's text (in-flight OT is the concurrency proof's job)
    &&& forall|e: nat, p: Path| #[trigger] own0.contains((e, p)) ==> {
        &&& k.buf0.dom().contains((e, p))
        &&& is_txt(k.c0, p) && k.buf0[(e, p)] == txt(k.c0, p)
        &&& !(k.excl)(p)
    }
    // disk equals cache for files no editor owns (excluded paths are never mirrored)
    &&& forall|p: Path| #![trigger get(disk0, p)]
        (!owned_any(own0, p) && !(k.excl)(p)) ==> get(disk0, p) == get(k.c0, p)
}

pub proof fn init_inv(k: K, own0: Set<(nat, nat)>, disk0: View)
    requires pre(k, own0, disk0),
    ensures inv(k, init_d(k, own0, disk0)),
{
    let d = init_d(k, own0, disk0);
    assert forall|e: nat, p: Path| #[trigger] d.own.contains((e, p)) implies app_ok(k.buf0[(e, p)], dl(d, p)) by {
        assert(dl(d, p) =~= Seq::<Rep>::empty());
    }
    assert forall|e: nat, p: Path| #[trigger] d.own.contains((e, p)) implies
        app_all(k.buf0[(e, p)], dl(d, p)) == txt(d.view, p) by {
        assert(dl(d, p) =~= Seq::<Rep>::empty());
    }
}

pub proof fn run(k: K, d: D, ps: Seq<Patch>)
    requires inv(k, d), replay(d.view, ps) == Some(k.f),
    ensures inv(k, fold_d(k, d, ps)), fold_d(k, d, ps).view == k.f,
    decreases ps.len(),
{
    if ps.len() > 0 {
        dstep_preserves(k, d, ps[0]);
        dstep_done(k, d, ps[0]);
        run(k, dstep(k, d, ps[0]), ps.drop_first());
    }
}

/// Main theorem for one ReceiveSyncMessage (git not running, writes succeed).
pub proof fn receive_sync_message_correct(
    k: K, own0: Set<(nat, nat)>, disk0: View, ps: Seq<Patch>,
)
    requires pre(k, own0, disk0), replay(k.c0, ps) == Some(k.f),
    ensures ({
        let dn = fold_d(k, init_d(k, own0, disk0), ps);
        // (1) cache = CRDT: equals the received document, plus empty files brought back for editors
        &&& (forall|p: Path| #![trigger get(dn.cache, p)]
                get(dn.cache, p) == get(k.f, p)
                || (get(k.f, p) is None
                    && get(dn.cache, p) == Some(Entry::Text(Seq::<int>::empty()))))
        // (2) every editor still owning a file: its buffer after the forwarded edits = cache text
        &&& (forall|e: nat, p: Path| #[trigger] dn.own.contains((e, p)) ==> {
                &&& is_txt(dn.cache, p)
                &&& app_ok(k.buf0[(e, p)], dl(dn, p))
                &&& app_all(k.buf0[(e, p)], dl(dn, p)) == txt(dn.cache, p)
            })
        // (3) after the writes, disk = cache for every non-excluded file no editor owns
        &&& (forall|p: Path| #![trigger get(fin_write(k, dn), p)]
                (!owned_any(dn.own, p) && !(k.excl)(p)) ==> get(fin_write(k, dn), p) == get(dn.cache, p))
    }),
{
    init_inv(k, own0, disk0);
    run(k, init_d(k, own0, disk0), ps);
    let dn = fold_d(k, init_d(k, own0, disk0), ps);
    assert forall|e: nat, p: Path| #[trigger] dn.own.contains((e, p)) implies {
        &&& is_txt(dn.cache, p)
        &&& app_ok(k.buf0[(e, p)], dl(dn, p))
        &&& app_all(k.buf0[(e, p)], dl(dn, p)) == txt(dn.cache, p)
    } by {
        assert(owned_any(dn.own, p));
    }
    let fw = fin_write(k, dn);
    assert forall|p: Path| #![trigger get(fw, p)]
        (!owned_any(dn.own, p) && !(k.excl)(p)) implies get(fw, p) == get(dn.cache, p) by {
        if !owned_any(dn.own, p) && !(k.excl)(p) {
            fin_get(k, dn, p);
            assert(get(dn.view, p) == get(k.f, p));
            if !dn.done.contains(p) {
                assert(get(dn.view, p) == get(k.c0, p));
                assert(get(dn.cache, p) == get(k.f, p));
                assert(!dn.pend.contains(p));
            } else if !(dn.pend.contains(p) && dn.cache.dom().contains(p)) {
                if !dn.cache.dom().contains(p) && get(dn.view, p) is Some {
                    assert(get(dn.cache, p) is None);
                }
            }
        }
    }
}

// ======================= message sequences (cache layer) =======================
// Across messages the cache may differ from the CRDT: a file revived as empty text for an editor
// is absent from the CRDT. `drift` is the exact relation this allows.
pub open spec fn drift(c: View, v: View) -> bool {
    forall|p: Path| #![trigger get(c, p)]
        get(c, p) == get(v, p) || (get(v, p) is None && get(c, p) == Some(Entry::Text(Seq::<int>::empty())))
}
pub open spec fn rel2_at(c: View, v: View, f: View, p: Path) -> bool {
    rel_at(c, v, f, p) || (get(v, p) is None && get(c, p) == Some(Entry::Text(Seq::<int>::empty())))
}
pub open spec fn rel2(c: View, v: View, f: View) -> bool {
    forall|p: Path| #[trigger] rel2_at(c, v, f, p)
}

pub proof fn step_preserves2(c: View, v: View, f: View, pt: Patch)
    requires rel2(c, v, f), step_view(v, pt) is Some,
    ensures
        cache_fits(c, pt),
        rel2(cache_step(c, f, pt), step_view(v, pt)->Some_0, f),
{
    let v1 = step_view(v, pt)->Some_0;
    let c1 = cache_step(c, f, pt);
    match pt {
        Patch::Splice(p, _, _) | Patch::DelSeq(p, _, _) => {
            assert(rel2_at(c, v, f, p));
            assert(txt(c, p) == txt(v, p));
        }
        _ => {}
    }
    assert forall|q: Path| #[trigger] rel2_at(c1, v1, f, q) by {
        assert(rel2_at(c, v, f, q));
    }
}

/// Over a whole message the cache stays within `drift` of the CRDT, starting from any drifted cache.
pub proof fn replay_preserves2(c: View, v: View, f: View, ps: Seq<Patch>)
    requires rel2(c, v, f), replay(v, ps) == Some(f),
    ensures drift(fold_cache(c, f, ps), f),
    decreases ps.len(),
{
    if ps.len() == 0 {
        assert forall|p: Path| #![trigger get(c, p)] get(c, p) == get(f, p)
            || (get(f, p) is None && get(c, p) == Some(Entry::Text(Seq::<int>::empty()))) by {
            assert(rel2_at(c, f, f, p));
        }
    } else {
        let v1 = step_view(v, ps[0])->Some_0;
        step_preserves2(c, v, f, ps[0]);
        replay_preserves2(cache_step(c, f, ps[0]), v1, f, ps.drop_first());
    }
}

pub proof fn drift_rel2(c: View, v: View, f: View)
    requires drift(c, v),
    ensures rel2(c, v, f),
{
    assert forall|p: Path| #[trigger] rel2_at(c, v, f, p) by {
        assert(get(c, p) == get(v, p) || (get(v, p) is None && get(c, p) == Some(Entry::Text(Seq::<int>::empty()))));
        assert(rel_at(c, v, f, p) || (get(v, p) is None && get(c, p) == Some(Entry::Text(Seq::<int>::empty()))));
    }
}

/// Any number of consecutive messages: the cache never panics on a delta and stays within `drift` of the CRDT.
pub proof fn message_sequence(c: View, v: View, f: View, ps: Seq<Patch>)
    requires drift(c, v), replay(v, ps) == Some(f),
    ensures drift(fold_cache(c, f, ps), f),
{
    drift_rel2(c, v, f);
    replay_preserves2(c, v, f, ps);
}

// ======================= git running =======================
// With git running, write_file only records the path in deferred_writes (daemon.rs write_file), so the
// disk is untouched. Every path the message touched (`done`) is a superset of what the non-git run
// would write; all other unowned non-excluded paths already have disk == cache.
pub proof fn git_running_correct(k: K, own0: Set<(nat, nat)>, disk0: View, ps: Seq<Patch>)
    requires pre(k, own0, disk0), replay(k.c0, ps) == Some(k.f),
    ensures ({
        let dn = fold_d(k, init_d(k, own0, disk0), ps);
        forall|p: Path| #![trigger get(disk0, p)]
            (!owned_any(own0, p) && !(k.excl)(p) && !dn.done.contains(p)) ==> get(disk0, p) == get(dn.cache, p)
    }),
{
    init_inv(k, own0, disk0);
    run(k, init_d(k, own0, disk0), ps);
    let dn = fold_d(k, init_d(k, own0, disk0), ps);
    assert forall|p: Path| #![trigger get(disk0, p)]
        (!owned_any(own0, p) && !(k.excl)(p) && !dn.done.contains(p)) implies get(disk0, p) == get(dn.cache, p) by {
        assert(get(dn.view, p) == get(k.c0, p));
        assert(get(dn.view, p) == get(k.f, p));
        assert(get(dn.cache, p) == get(k.f, p));
    }
}

// ======================= chaining document.rs and daemon.rs =======================
/// `init_d` assumes the cache right after receive_sync_message_log_patches is exactly `f`. This is that
/// step: starting from cache == CRDT (c0), the per-patch cache updates produce `f` (so the daemon
/// theorem's initial state is the real one, not a free assumption).
pub proof fn init_cache_justified(k: K, ps: Seq<Patch>)
    requires replay(k.c0, ps) == Some(k.f),
    ensures forall|p: Path| #![trigger get(fold_cache(k.c0, k.f, ps), p)] get(fold_cache(k.c0, k.f, ps), p) == get(k.f, p),
{
    assert forall|p: Path| #[trigger] rel_at(k.c0, k.c0, k.f, p) by {}
    replay_preserves(k.c0, k.c0, k.f, ps);
}

/// Whole pipeline for one message: document.rs cache update, then the daemon effect loop.
pub proof fn pipeline_correct(k: K, own0: Set<(nat, nat)>, disk0: View, ps: Seq<Patch>)
    requires pre(k, own0, disk0), replay(k.c0, ps) == Some(k.f),
    ensures
        init_d(k, own0, disk0).cache == k.f,
        forall|p: Path| #![trigger get(fold_cache(k.c0, k.f, ps), p)] get(fold_cache(k.c0, k.f, ps), p) == get(init_d(k, own0, disk0).cache, p),
        ({
            let dn = fold_d(k, init_d(k, own0, disk0), ps);
            forall|p: Path| #![trigger get(fin_write(k, dn), p)]
                (!owned_any(dn.own, p) && !(k.excl)(p)) ==> get(fin_write(k, dn), p) == get(dn.cache, p)
        }),
{
    init_cache_justified(k, ps);
    receive_sync_message_correct(k, own0, disk0, ps);
}

// ======================= daemon layer from a drifted cache =======================
// Before a message the cache may hold phantom files: empty text for a path the CRDT lacks (revived for
// an editor). Reduction: run the CRDT patches on the *cache* instead of the CRDT. The result `fp`
// equals the received document `f` except for untouched phantoms (`drift(fp, f)`), and equals it
// exactly at every path a PutText/Delete/PutBytes patch hit, which are the only paths where
// cache_step reads the final document. So the daemon theorem applies to (c0 := cache, f := fp).
pub open spec fn resets_one(pt: Patch, p: Path) -> bool {
    match pt {
        Patch::PutText(q) | Patch::Delete(q) | Patch::PutBytes(q, _) => q == p,
        _ => false,
    }
}
pub open spec fn resets(ps: Seq<Patch>, p: Path) -> bool
    decreases ps.len(),
{
    ps.len() > 0 && (resets_one(ps[0], p) || resets(ps.drop_first(), p))
}

proof fn step_drift(vp: View, v: View, pt: Patch)
    requires drift(vp, v), step_view(v, pt) is Some,
    ensures
        step_view(vp, pt) is Some,
        drift(step_view(vp, pt)->Some_0, step_view(v, pt)->Some_0),
        forall|p: Path| get(vp, p) == get(v, p) ==>
            #[trigger] get(step_view(vp, pt)->Some_0, p) == get(step_view(v, pt)->Some_0, p),
        forall|p: Path| resets_one(pt, p) ==>
            #[trigger] get(step_view(vp, pt)->Some_0, p) == get(step_view(v, pt)->Some_0, p),
{
    let v1 = step_view(v, pt)->Some_0;
    match pt {
        Patch::Splice(q, _, _) | Patch::DelSeq(q, _, _) => {
            assert(get(vp, q) == get(v, q));
            assert(txt(vp, q) == txt(v, q));
            assert(is_txt(vp, q));
        }
        _ => {}
    }
    let vp1 = step_view(vp, pt)->Some_0;
    assert forall|p: Path| #![trigger get(vp1, p)]
        get(vp1, p) == get(v1, p) || (get(v1, p) is None && get(vp1, p) == Some(Entry::Text(Seq::<int>::empty()))) by {
        assert(get(vp, p) == get(v, p) || (get(v, p) is None && get(vp, p) == Some(Entry::Text(Seq::<int>::empty()))));
    }
}

pub proof fn replay_drift(vp: View, v: View, f: View, ps: Seq<Patch>)
    requires drift(vp, v), replay(v, ps) == Some(f),
    ensures
        replay(vp, ps) is Some,
        drift(replay(vp, ps)->Some_0, f),
        forall|p: Path| get(vp, p) == get(v, p) ==> #[trigger] get(replay(vp, ps)->Some_0, p) == get(f, p),
        forall|p: Path| resets(ps, p) ==> #[trigger] get(replay(vp, ps)->Some_0, p) == get(f, p),
    decreases ps.len(),
{
    if ps.len() > 0 {
        step_drift(vp, v, ps[0]);
        let v1 = step_view(v, ps[0])->Some_0;
        let vp1 = step_view(vp, ps[0])->Some_0;
        replay_drift(vp1, v1, f, ps.drop_first());
        let fp = replay(vp, ps)->Some_0;
        assert(fp == replay(vp1, ps.drop_first())->Some_0);
        assert forall|p: Path| resets(ps, p) implies #[trigger] get(fp, p) == get(f, p) by {
            if resets_one(ps[0], p) {
                assert(get(vp1, p) == get(v1, p));
            }
        }
        assert forall|p: Path| get(vp, p) == get(v, p) implies #[trigger] get(fp, p) == get(f, p) by {
            assert(get(vp1, p) == get(v1, p));
        }
    } else {
        assert forall|p: Path| get(vp, p) == get(v, p) implies #[trigger] get(vp, p) == get(f, p) by {}
    }
}

/// gfin sees the final document only at reset paths, where fp and f agree: the cache update is the same.
proof fn fold_cache_same(c: View, f: View, fp: View, ps: Seq<Patch>)
    requires forall|p: Path| resets(ps, p) ==> #[trigger] get(fp, p) == get(f, p),
    ensures fold_cache(c, f, ps) == fold_cache(c, fp, ps),
    decreases ps.len(),
{
    if ps.len() > 0 {
        let pt = ps[0];
        assert forall|p: Path| resets(ps.drop_first(), p) implies #[trigger] get(fp, p) == get(f, p) by {
            assert(resets(ps, p));
        }
        match pt {
            Patch::PutText(p) | Patch::Delete(p) => {
                assert(resets(ps, p));
                assert(get(fp, p) == get(f, p));
                assert(is_txt(f, p) == is_txt(fp, p));
                assert(gfin(f, p) == gfin(fp, p));
                assert(cache_step(c, f, pt) == cache_step(c, fp, pt));
            }
            _ => {}
        }
        fold_cache_same(cache_step(c, f, pt), f, fp, ps.drop_first());
    }
}

/// Daemon theorem when the cache before the message may hold phantom files. `cp` is the cache (and,
/// by pre, the editors' text and the disk's mirror) before the message; `c0` is the CRDT. Conclusions
/// are those of receive_sync_message_correct for the document `fp`, which is within drift of `f`.
pub proof fn receive_sync_message_drifted(
    k: K, cp: View, own0: Set<(nat, nat)>, disk0: View, ps: Seq<Patch>,
)
    requires
        drift(cp, k.c0), replay(k.c0, ps) == Some(k.f),
        pre(K { c0: cp, f: replay(cp, ps)->Some_0, ..k }, own0, disk0),
    ensures
        ({
            let fp = replay(cp, ps)->Some_0;
            let k2 = K { c0: cp, f: fp, ..k };
            let dn = fold_d(k2, init_d(k2, own0, disk0), ps);
            &&& drift(fp, k.f)
            &&& fold_cache(cp, k.f, ps) == fold_cache(cp, fp, ps)
            &&& (forall|p: Path| #![trigger get(dn.cache, p)]
                    get(dn.cache, p) == get(fp, p)
                    || (get(fp, p) is None && get(dn.cache, p) == Some(Entry::Text(Seq::<int>::empty()))))
            &&& (forall|e: nat, p: Path| #[trigger] dn.own.contains((e, p)) ==> {
                    &&& is_txt(dn.cache, p)
                    &&& app_ok(k.buf0[(e, p)], dl(dn, p))
                    &&& app_all(k.buf0[(e, p)], dl(dn, p)) == txt(dn.cache, p)
                })
            &&& (forall|p: Path| #![trigger get(fin_write(k2, dn), p)]
                    (!owned_any(dn.own, p) && !(k.excl)(p)) ==> get(fin_write(k2, dn), p) == get(dn.cache, p))
        }),
{
    replay_drift(cp, k.c0, k.f, ps);
    let fp = replay(cp, ps)->Some_0;
    let k2 = K { c0: cp, f: fp, ..k };
    assert forall|p: Path| resets(ps, p) implies #[trigger] get(fp, p) == get(k.f, p) by {}
    fold_cache_same(cp, k.f, fp, ps);
    receive_sync_message_correct(k2, own0, disk0, ps);
}

}
}
mod comp {
use vstd::prelude::*;
use crate::conc;
use crate::bnd;
verus! {

// ASSUMED bridge (trusted, like the OT axioms): the OT crate's `apply` of the op that the daemon builds
// for a forwarded delta `r` (op `enc(r)`) replaces chars [i, i+n) with s. Text is mapped int -> char.
pub uninterp spec fn tc(x: int) -> char;
pub uninterp spec fn enc(r: bnd::Rep) -> int;
pub open spec fn tchars(t: Seq<int>) -> Seq<char> { t.map_values(|x: int| tc(x)) }

#[verifier::external_body]
pub proof fn axiom_enc(t: Seq<int>, r: bnd::Rep)
    requires bnd::rep_ok(t, r.i, r.n),
    ensures conc::ap(tchars(t), enc(r)) == tchars(bnd::app(t, r)),
{}

/// The world after the daemon pushed the forwarded deltas `ds` through `OTServer::apply_crdt_change`, in order.
pub open spec fn wfold(w: conc::W, ds: Seq<bnd::Rep>) -> conc::W
    decreases ds.len(),
{
    if ds.len() == 0 { w } else { conc::crdt_step(wfold(w, ds.drop_last()), enc(ds.last())) }
}

pub proof fn wfold_ok(w: conc::W, t: Seq<int>, ds: Seq<bnd::Rep>)
    requires conc::inv(w), w.srv.cur == tchars(t), bnd::app_ok(t, ds),
    ensures
        conc::inv(wfold(w, ds)),
        wfold(w, ds).srv.cur == tchars(bnd::app_all(t, ds)),
    decreases ds.len(),
{
    if ds.len() > 0 {
        let pre = ds.drop_last();
        wfold_ok(w, t, pre);
        let w1 = wfold(w, pre);
        let r = ds.last();
        assert(bnd::rep_ok(bnd::app_all(t, pre), r.i, r.n));
        axiom_enc(bnd::app_all(t, pre), r);
        conc::lemma_crdt_step(w1, enc(r));
    }
}

/// Boundary + concurrency: for any in-flight editor/daemon state satisfying the protocol invariant whose
/// OT server holds the daemon's text, receiving a sync message keeps the protocol invariant (so editor and
/// daemon still converge when quiescent), never feeds the server a delta that does not fit, and leaves the
/// server's current_content equal to the daemon's cache text.
pub proof fn message_keeps_world(
    k: bnd::K, own0: Set<(nat, nat)>, disk0: bnd::View, ps: Seq<bnd::Patch>,
    w: conc::W, e: nat, p: bnd::Path,
)
    requires
        bnd::pre(k, own0, disk0), bnd::replay(k.c0, ps) == Some(k.f),
        own0.contains((e, p)), bnd::fold_d(k, bnd::init_d(k, own0, disk0), ps).own.contains((e, p)),
        conc::inv(w), w.srv.cur == tchars(k.buf0[(e, p)]),
    ensures ({
        let dn = bnd::fold_d(k, bnd::init_d(k, own0, disk0), ps);
        &&& conc::inv(wfold(w, bnd::dl(dn, p)))
        &&& wfold(w, bnd::dl(dn, p)).srv.cur == tchars(bnd::txt(dn.cache, p))
    }),
{
    bnd::receive_sync_message_correct(k, own0, disk0, ps);
    let dn = bnd::fold_d(k, bnd::init_d(k, own0, disk0), ps);
    wfold_ok(w, k.buf0[(e, p)], bnd::dl(dn, p));
}


// ---------- editor rejects a daemon edit (vscode-plugin extension.ts: `rejected an applyEdit, sending empty delta`) ----------
// The plugin drops the daemon's message without applying it, does NOT bump `revision.daemon`, and sends an
// empty delta with `revision.daemon` and `revision.editor += 1`. The daemon reads the empty delta as the
// identity op, transforms it through its queue, and resends every unconfirmed op, so the editor gets the
// rejected op again. In the model that is: pop the message, then an editor edit by the identity op.
// ASSUMED: an identity op exists (an empty `EditorTextDelta` becomes an empty `OperationSeq`, which
// `force_apply` pads with a full retain).
pub uninterp spec fn idop() -> int;
#[verifier::external_body]
pub proof fn axiom_idop(d: Seq<char>)
    ensures conc::ap(d, idop()) == d,
{}

pub open spec fn ed_reject(w: conc::W) -> conc::W {
    conc::W {
        srv: w.srv,
        ed: conc::Ed { buf: w.ed.buf, rd: w.ed.rd, re: w.ed.re + 1 },
        up: w.up.push(conc::Up { rev: w.ed.rd, op: idop() }),
        down: w.down.drop_first(),
    }
}

/// Rejecting a current daemon message preserves the protocol invariant (so editor and daemon still converge:
/// the daemon resends the op). Note the editor buffer did not change.
pub proof fn lemma_ed_reject(w: conc::W)
    requires conc::inv(w), w.down.len() > 0, w.down[0].rev == w.ed.re,
    ensures conc::inv(ed_reject(w)), ed_reject(w).ed.buf == w.ed.buf,
{
    let s = w.srv; let e = w.ed; let c = conc::confirmed(s);
    let w2 = ed_reject(w);
    let m = w.down[0];
    assert(m.rev <= s.er);
    assert(s.er == e.re);
    assert(w.up.len() == 0);
    assert forall|i: int| 0 <= i < w2.down.len() implies (#[trigger] w2.down[i]).rev <= s.er by {
        assert(w2.down[i] == w.down[i + 1]);
    }
    assert forall|i: int| 0 <= i < w2.down.len() && (#[trigger] w2.down[i]).rev == s.er
        implies c <= w2.down[i].g < s.dr && w2.down[i].op == s.q[w2.down[i].g - c] by {
        assert(w2.down[i] == w.down[i + 1]);
    }
    assert(conc::up_ops(w2.up) =~= Seq::<int>::empty().push(idop()));
    assert(conc::up_ops(w.up) =~= Seq::<int>::empty());
    let base = conc::fold(s.lc, s.q.subrange(0, e.rd - c));
    assert(base == e.buf);
    conc::lemma_fold_snoc(base, Seq::<int>::empty(), idop());
    axiom_idop(base);
    assert(w2.up.len() == 1);
    assert forall|i: int| 0 <= i < w2.up.len() implies (#[trigger] w2.up[i]).rev == e.rd by {
        assert(w2.up[i] == conc::Up { rev: e.rd, op: idop() });
    }
}
}
}

// (authored by agents) Replacement-of-a-text-object proof: types.rs parsing + document.rs rewrite +
// daemon.rs effects + editor OT server with in-flight messages, composed from boundary.rs and concurrency/.
mod rp {
use vstd::prelude::*;
use crate::conc;
use crate::bnd;
use crate::bnd::{Patch, Path, Rep, Entry, View};
use crate::comp;
verus! {

// ---------------------------------------------------------------------------------------------
// Raw patches: what Automerge emits (`Patch { path, action }`), one constructor per shape that
// types.rs `TryFrom<&Patch> for PatchEffect` distinguishes. Path = name under "files".
// ---------------------------------------------------------------------------------------------
pub enum Raw {
    PutMapText(Path),            // path ["files"], PutMap { key, value: (Object(Text), _) }
    PutMapBytes(Path, Seq<int>), // path ["files"], PutMap { key, value: Scalar(Bytes) }
    DeleteMap(Path),             // path ["files"], DeleteMap { key }
    ConflictMap(Path),           // path ["files"], Conflict { prop: Map(key) }
    Splice(Path, int, Seq<int>), // path ["files", key], SpliceText { index, value }
    DelSeq(Path, int, int),      // path ["files", key], DeleteSeq { index, length }
    Unsupported,                 // empty path PutMap "files", and every shape that is ignored
}

/// types.rs PatchEffect
pub enum Eff { Change(Path, Rep), Removal(Path), Bytes(Path, Seq<int>), NoEffect }

/// Visible text object per path before / after applying the message (document.rs `before`, `text_obj`).
pub struct Objs { pub before: Map<Path, nat>, pub now: Map<Path, nat> }
pub open spec fn switched(o: Objs, p: Path) -> bool {
    o.before.dom().contains(p) && o.now.dom().contains(p) && o.before[p] != o.now[p]
}

/// document.rs `replaced_text_objects_as_puts`: a Conflict at a key whose visible text object changed
/// becomes PutMap(Text).
pub open spec fn rewrite(r: Raw, o: Objs) -> Raw {
    match r {
        Raw::ConflictMap(p) => if switched(o, p) { Raw::PutMapText(p) } else { r },
        _ => r,
    }
}

/// types.rs `TryFrom<&Patch> for PatchEffect` / `PatchEffect::from_patch`, restricted to these shapes.
/// PutMap(Text) -> FileRemoval (the fix); SpliceText -> delta [Retain(index), Insert(value)];
/// DeleteSeq -> delta [Retain(index), Delete(length)].
pub open spec fn effect(r: Raw) -> Eff {
    match r {
        Raw::PutMapText(p) => Eff::Removal(p),
        Raw::PutMapBytes(p, b) => Eff::Bytes(p, b),
        Raw::DeleteMap(p) => Eff::Removal(p),
        Raw::ConflictMap(_) => Eff::NoEffect,
        Raw::Splice(p, i, s) => Eff::Change(p, Rep { i, n: 0, s }),
        Raw::DelSeq(p, i, n) => Eff::Change(p, Rep { i, n, s: Seq::empty() }),
        Raw::Unsupported => Eff::NoEffect,
    }
}
/// The behaviour before fca5b71: PutMap(Text) -> FileChange with an EMPTY delta (a no-op).
pub open spec fn effect_old(r: Raw) -> Eff {
    match r {
        Raw::PutMapText(p) => Eff::Change(p, Rep { i: 0, n: 0, s: Seq::empty() }),
        _ => effect(r),
    }
}

/// TRUSTED (Automerge): the meaning of each emitted patch, read against the previous visible state.
/// A PutMap(Text), or a Conflict whose visible text object changed, makes a fresh EMPTY text at the path;
/// later SpliceText/DeleteSeq at that path edit that fresh text.
pub open spec fn sem(r: Raw, o: Objs) -> Patch {
    match r {
        Raw::PutMapText(p) => Patch::PutText(p),
        Raw::PutMapBytes(p, b) => Patch::PutBytes(p, b),
        Raw::DeleteMap(p) => Patch::Delete(p),
        Raw::ConflictMap(p) => if switched(o, p) { Patch::PutText(p) } else { Patch::Conflict(p) },
        Raw::Splice(p, i, s) => Patch::Splice(p, i, s),
        Raw::DelSeq(p, i, n) => Patch::DelSeq(p, i, n),
        Raw::Unsupported => Patch::Conflict(0),
    }
}

/// What the Rust code does with an effect, in boundary.rs terms. FileRemoval is one branch in daemon.rs
/// and one cache update in document.rs whether it came from PutMap or DeleteMap: it is `PutText`.
pub open spec fn eff_patch(e: Eff) -> Patch {
    match e {
        Eff::Change(p, r) => if r.n == 0 { Patch::Splice(p, r.i, r.s) } else { Patch::DelSeq(p, r.i, r.n) },
        Eff::Removal(p) => Patch::PutText(p),
        Eff::Bytes(p, b) => Patch::PutBytes(p, b),
        Eff::NoEffect => Patch::Conflict(0),
    }
}
/// Normal form: patches the code cannot tell apart.
pub open spec fn canon(pt: Patch) -> Patch {
    match pt {
        Patch::Delete(p) => Patch::PutText(p),
        Patch::DelSeq(p, i, n) => if n == 0 { Patch::Splice(p, i, Seq::empty()) } else { pt },
        Patch::Conflict(_) => Patch::Conflict(0),
        _ => pt,
    }
}

pub open spec fn sems(rs: Seq<Raw>, o: Objs) -> Seq<Patch> { rs.map_values(|r: Raw| sem(r, o)) }
/// The patch list the daemon and the cache actually process.
pub open spec fn codes(rs: Seq<Raw>, o: Objs) -> Seq<Patch> {
    rs.map_values(|r: Raw| eff_patch(effect(rewrite(r, o))))
}
pub open spec fn canons(ps: Seq<Patch>) -> Seq<Patch> { ps.map_values(|pt: Patch| canon(pt)) }

/// Parsing is faithful: for every shape, what types.rs + the rewrite compute is the normal form of the
/// patch's meaning.
pub proof fn parse_ok(r: Raw, o: Objs)
    ensures eff_patch(effect(rewrite(r, o))) == canon(sem(r, o)),
{}

pub proof fn codes_are_canons(rs: Seq<Raw>, o: Objs)
    ensures codes(rs, o) =~= canons(sems(rs, o)),
{
    assert forall|i: int| 0 <= i < rs.len() implies codes(rs, o)[i] == canons(sems(rs, o))[i] by {
        parse_ok(rs[i], o);
    }
}

// ---- the daemon/cache cannot tell a patch from its normal form (except in the ghost `view`) ----
pub open spec fn same_nv(a: bnd::D, b: bnd::D) -> bool {
    a.cache == b.cache && a.own == b.own && a.deltas == b.deltas && a.disk == b.disk
        && a.pend == b.pend && a.done == b.done
}
proof fn dstep_nv(k: bnd::K, d1: bnd::D, d2: bnd::D, pt: Patch)
    requires same_nv(d1, d2),
    ensures same_nv(bnd::dstep(k, d1, pt), bnd::dstep(k, d2, pt)),
{}
proof fn dstep_canon(k: bnd::K, d: bnd::D, pt: Patch)
    ensures same_nv(bnd::dstep(k, d, pt), bnd::dstep(k, d, canon(pt))),
{}
proof fn fold_nv(k: bnd::K, d1: bnd::D, d2: bnd::D, ps: Seq<Patch>)
    requires same_nv(d1, d2),
    ensures same_nv(bnd::fold_d(k, d1, ps), bnd::fold_d(k, d2, canons(ps))),
    decreases ps.len(),
{
    if ps.len() > 0 {
        dstep_canon(k, d1, ps[0]);
        dstep_nv(k, d1, d2, canon(ps[0]));
        assert(canons(ps).drop_first() =~= canons(ps.drop_first()));
        assert(canons(ps)[0] == canon(ps[0]));
        let d1n = bnd::dstep(k, d1, ps[0]);
        let d2n = bnd::dstep(k, d2, canon(ps[0]));
        fold_nv(k, d1n, d2n, ps.drop_first());
    }
}
proof fn cache_canon(c: View, f: View, ps: Seq<Patch>)
    ensures bnd::fold_cache(c, f, canons(ps)) == bnd::fold_cache(c, f, ps),
    decreases ps.len(),
{
    if ps.len() > 0 {
        assert(canons(ps).drop_first() =~= canons(ps.drop_first()));
        assert(canons(ps)[0] == canon(ps[0]));
        assert(bnd::cache_step(c, f, canon(ps[0])) == bnd::cache_step(c, f, ps[0]));
        cache_canon(bnd::cache_step(c, f, ps[0]), f, ps.drop_first());
    }
}

proof fn wfold_up(w: conc::W, ds: Seq<bnd::Rep>)
    ensures comp::wfold(w, ds).up == w.up,
    decreases ds.len(),
{
    if ds.len() > 0 { wfold_up(w, ds.drop_last()); }
}

// ---- draining the editor/daemon channels (concurrency/ world) ----
pub open spec fn drain(w: conc::W) -> conc::W
    decreases w.up.len(), w.down.len(),
{
    if w.up.len() > 0 { drain(conc::srv_recv(w)) }
    else if w.down.len() > 0 { drain(conc::ed_recv(w)) }
    else { w }
}
/// Delivering every in-flight message (editor edits first, then daemon messages, each FIFO) reaches a
/// quiescent world satisfying the invariant, in which the editor holds the daemon's text. Without
/// in-flight editor edits the daemon's text is unchanged by the drain.
pub proof fn drain_ok(w: conc::W)
    requires conc::inv(w),
    ensures
        conc::inv(drain(w)), drain(w).up.len() == 0, drain(w).down.len() == 0,
        drain(w).ed.buf == drain(w).srv.cur,
        w.up.len() == 0 ==> drain(w).srv.cur == w.srv.cur,
    decreases w.up.len(), w.down.len(),
{
    if w.up.len() > 0 {
        conc::lemma_srv_recv(w);
        drain_ok(conc::srv_recv(w));
    } else if w.down.len() > 0 {
        conc::lemma_ed_recv(w);
        drain_ok(conc::ed_recv(w));
    } else {
        conc::theorem_quiescent_agreement(w);
    }
}

// ---------------------------------------------------------------------------------------------
// THE THEOREM. A batch of raw patches (any number of replacements of any paths, mixed with
// edits, deletions, byte files), with an editor `e` holding `p` open and any in-flight editor edits
// and daemon messages `w`:
//  - document.rs cache update, run over the effects types.rs computes, yields exactly the CRDT `f`;
//  - after the daemon.rs effect loop the cache is `f` (up to revived-empty files);
//  - the editor's OT server text becomes the cache text, the protocol invariant survives, and once
//    all in-flight messages are delivered the editor buffer equals the daemon text (= CRDT text when
//    no editor edit was in flight).
// ---------------------------------------------------------------------------------------------
pub proof fn replace_e2e(
    k: bnd::K, own0: Set<(nat, nat)>, disk0: View, rs: Seq<Raw>, o: Objs,
    w: conc::W, e: nat, p: Path,
)
    requires
        bnd::pre(k, own0, disk0),
        // TRUSTED: Automerge's patches, read by `sem`, replay the visible state before to the one after
        bnd::replay(k.c0, sems(rs, o)) == Some(k.f),
        own0.contains((e, p)),
        bnd::fold_d(k, bnd::init_d(k, own0, disk0), codes(rs, o)).own.contains((e, p)),
        conc::inv(w), w.srv.cur == comp::tchars(k.buf0[(e, p)]),
    ensures ({
        let cs = codes(rs, o);
        let dn = bnd::fold_d(k, bnd::init_d(k, own0, disk0), cs);
        let w1 = comp::wfold(w, bnd::dl(dn, p));
        let wd = drain(w1);
        &&& forall|q: Path| #![trigger bnd::get(bnd::fold_cache(k.c0, k.f, cs), q)]
                bnd::get(bnd::fold_cache(k.c0, k.f, cs), q) == bnd::get(k.f, q)
        &&& forall|q: Path| #![trigger bnd::get(dn.cache, q)]
                bnd::get(dn.cache, q) == bnd::get(k.f, q)
                || (bnd::get(k.f, q) is None && bnd::get(dn.cache, q) == Some(Entry::Text(Seq::<int>::empty())))
        &&& conc::inv(w1) && w1.srv.cur == comp::tchars(bnd::txt(dn.cache, p))
        &&& conc::inv(wd) && wd.up.len() == 0 && wd.down.len() == 0 && wd.ed.buf == wd.srv.cur
        &&& (w.up.len() == 0 ==> wd.ed.buf == comp::tchars(bnd::txt(dn.cache, p)))
    }),
{
    let ss = sems(rs, o);
    let cs = codes(rs, o);
    codes_are_canons(rs, o);
    let d0 = bnd::init_d(k, own0, disk0);
    // daemon.rs loop: same as the loop over the meanings, off the ghost view
    fold_nv(k, d0, d0, ss);
    // document.rs cache update
    cache_canon(k.c0, k.f, ss);
    bnd::init_cache_justified(k, ss);
    // boundary + concurrency on the meaning list
    let dn_s = bnd::fold_d(k, d0, ss);
    let dn = bnd::fold_d(k, d0, cs);
    assert(cs =~= canons(ss));
    assert(dn.own.contains((e, p)));
    assert(dn_s.own.contains((e, p)));
    comp::message_keeps_world(k, own0, disk0, ss, w, e, p);
    bnd::receive_sync_message_correct(k, own0, disk0, ss);
    assert(bnd::dl(dn, p) == bnd::dl(dn_s, p));
    assert(bnd::get(dn.cache, p) == bnd::get(dn_s.cache, p));
    let w1 = comp::wfold(w, bnd::dl(dn, p));
    assert(cs == canons(ss));
    assert(bnd::fold_cache(k.c0, k.f, cs) == bnd::fold_cache(k.c0, k.f, ss));
    assert forall|q: Path| #![trigger bnd::get(bnd::fold_cache(k.c0, k.f, cs), q)]
        bnd::get(bnd::fold_cache(k.c0, k.f, cs), q) == bnd::get(k.f, q) by {
        assert(bnd::get(bnd::fold_cache(k.c0, k.f, ss), q) == bnd::get(k.f, q));
    }
    wfold_up(w, bnd::dl(dn, p));
    drain_ok(w1);
    assert forall|q: Path| #![trigger bnd::get(dn.cache, q)]
        bnd::get(dn.cache, q) == bnd::get(k.f, q)
        || (bnd::get(k.f, q) is None && bnd::get(dn.cache, q) == Some(Entry::Text(Seq::<int>::empty()))) by {
        assert(bnd::get(dn_s.cache, q) == bnd::get(dn.cache, q));
    }
}

// ---------------------------------------------------------------------------------------------
// Concrete replacement: the old text "ab" is replaced by "y" (patches: PutMap(Text), SpliceText "y").
// The fixed effects give cache == "y"; the pre-fix effects (empty FileChange) give "yab".
// ---------------------------------------------------------------------------------------------
pub open spec fn ex_c0() -> View { Map::<Path, Entry>::empty().insert(7, Entry::Text(seq![1int, 2int])) }
pub open spec fn ex_f() -> View { Map::<Path, Entry>::empty().insert(7, Entry::Text(seq![3int])) }
pub open spec fn ex_raws() -> Seq<Raw> { seq![Raw::PutMapText(7), Raw::Splice(7, 0, seq![3int])] }
pub open spec fn ex_objs() -> Objs { Objs { before: Map::empty(), now: Map::empty() } }
pub open spec fn codes_old(rs: Seq<Raw>, o: Objs) -> Seq<Patch> {
    rs.map_values(|r: Raw| eff_patch(effect_old(rewrite(r, o))))
}
pub proof fn example_fixed_and_old()
    ensures
        bnd::replay(ex_c0(), sems(ex_raws(), ex_objs())) == Some(ex_f()),
        bnd::get(bnd::fold_cache(ex_c0(), ex_f(), codes(ex_raws(), ex_objs())), 7) == Some(Entry::Text(seq![3int])),
        bnd::get(bnd::fold_cache(ex_c0(), ex_f(), codes_old(ex_raws(), ex_objs())), 7)
            == Some(Entry::Text(seq![3int, 1int, 2int])),
{
    let o = ex_objs();
    let rs = ex_raws();
    reveal_with_fuel(bnd::replay, 3);
    reveal_with_fuel(bnd::fold_cache, 3);
    assert(sems(rs, o) =~= seq![Patch::PutText(7), Patch::Splice(7, 0, seq![3int])]);
    assert(codes(rs, o) =~= seq![Patch::PutText(7), Patch::Splice(7, 0, seq![3int])]);
    assert(codes_old(rs, o) =~= seq![Patch::Splice(7, 0, Seq::empty()), Patch::Splice(7, 0, seq![3int])]);
    let v1 = bnd::step_view(ex_c0(), Patch::PutText(7))->Some_0;
    assert(bnd::txt(v1, 7) =~= Seq::<int>::empty());
    assert(bnd::rep(Seq::<int>::empty(), 0, 0, seq![3int]) =~= seq![3int]);
    assert(bnd::step_view(v1, Patch::Splice(7, 0, seq![3int]))->Some_0 =~= ex_f());
    let c1 = bnd::cache_step(ex_c0(), ex_f(), Patch::PutText(7));
    assert(bnd::get(c1, 7) == Some(Entry::Text(Seq::<int>::empty())));
    let c1o = bnd::cache_step(ex_c0(), ex_f(), Patch::Splice(7, 0, Seq::empty()));
    assert(bnd::txt(ex_c0(), 7) =~= seq![1int, 2int]);
    assert(bnd::rep(seq![1int, 2int], 0, 0, Seq::empty()) =~= seq![1int, 2int]);
    assert(bnd::txt(c1o, 7) =~= seq![1int, 2int]);
    assert(bnd::rep(seq![1int, 2int], 0, 0, seq![3int]) =~= seq![3int, 1int, 2int]);
    assert(bnd::rep(Seq::<int>::empty(), 0, 0, seq![3int]) =~= seq![3int]);
}

}
}

fn main() {}
