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
fn main() {}
