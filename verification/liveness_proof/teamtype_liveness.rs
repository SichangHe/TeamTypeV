// Verus liveness proof for the TeamType editor/daemon OT pipeline. Lines up to "LIVENESS" are copied
// verbatim from ../concurrency/teamtype_concurrency.rs (model + inductive invariant, no ot.rs refinement);
// the new part is the section after the marker.
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
// LIVENESS: once edits and CRDT changes stop, delivering the in-flight messages reaches quiescence.
// =====================================================================================
pub open spec fn quiescent(w: W) -> bool { w.up.len() == 0 && w.down.len() == 0 }

// a delivery step: the daemon receives the oldest editor edit, or the editor receives the oldest
// daemon message (no crdt_step / ed_local: "edits have stopped")
pub open spec fn is_delivery(w: W, w2: W) -> bool {
    (w.up.len() > 0 && w2 == srv_recv(w)) || (w.down.len() > 0 && w2 == ed_recv(w))
}

// no deadlock: unless quiescent, some delivery is enabled
pub proof fn lemma_no_deadlock(w: W)
    requires !quiescent(w),
    ensures w.up.len() > 0 || w.down.len() > 0,
{}

// lexicographic rank (up.len, down.len): every delivery strictly decreases it. srv_recv drops `up` by
// one (and may grow `down`); ed_recv leaves `up` alone and drops `down` by one.
pub open spec fn rank_lt(a: W, b: W) -> bool {
    a.up.len() < b.up.len() || (a.up.len() == b.up.len() && a.down.len() < b.down.len())
}

pub proof fn lemma_delivery(w: W, w2: W)
    requires inv(w), is_delivery(w, w2),
    ensures inv(w2), rank_lt(w2, w),
{
    if w.up.len() > 0 && w2 == srv_recv(w) {
        lemma_srv_recv(w);
        assert(w2.up.len() == w.up.len() - 1);
    } else {
        lemma_ed_recv(w);
        assert(w2.up == w.up);
        assert(w2.down.len() == w.down.len() - 1);
    }
}

// Liveness: every delivery-only execution that continues while not quiescent reaches a quiescent state
// (no scheduler, fair or not, can avoid it: each step consumes rank), and there inv + agreement hold.
pub proof fn lemma_run_ends(f: spec_fn(nat) -> W, i: nat)
    requires
        inv(f(i)),
        forall|j: nat| j >= i && !quiescent(#[trigger] f(j)) ==> is_delivery(f(j), f(j + 1)),
    ensures
        exists|n: nat| #![trigger f(n)] n >= i && quiescent(f(n)) && inv(f(n))
            && f(n).ed.buf == f(n).srv.cur && f(n).ed.rd == f(n).srv.dr,
    decreases f(i).up.len(), f(i).down.len(),
{
    if quiescent(f(i)) {
        theorem_quiescent_agreement(f(i));
        assert(quiescent(f(i)) && inv(f(i)) && f(i).ed.buf == f(i).srv.cur && f(i).ed.rd == f(i).srv.dr);
    } else {
        assert(is_delivery(f(i), f(i + 1)));
        lemma_delivery(f(i), f(i + 1));
        lemma_run_ends(f, i + 1);
        let n = choose|n: nat| #![trigger f(n)] n >= i + 1 && quiescent(f(n)) && inv(f(n))
            && f(n).ed.buf == f(n).srv.cur && f(n).ed.rd == f(n).srv.dr;
        assert(n >= i && quiescent(f(n)) && inv(f(n)) && f(n).ed.buf == f(n).srv.cur);
    }
}

// Existence form: from any invariant state there is a delivery-only execution to a quiescent state.
// (Together with lemma_delivery: ALL delivery-only executions get there.)
pub proof fn lemma_drain(w: W) -> (w2: W)
    requires inv(w),
    ensures inv(w2), quiescent(w2), w2.ed.buf == w2.srv.cur, w2.ed.rd == w2.srv.dr,
    decreases w.up.len(), w.down.len(),
{
    if quiescent(w) {
        theorem_quiescent_agreement(w);
        w
    } else if w.up.len() > 0 {
        lemma_srv_recv(w);
        lemma_delivery(w, srv_recv(w));
        lemma_drain(srv_recv(w))
    } else {
        lemma_ed_recv(w);
        lemma_delivery(w, ed_recv(w));
        lemma_drain(ed_recv(w))
    }
}

// Composition (several editors; each editor/daemon pair is its own world). If every pair is quiescent
// and the daemons' current texts agree (ASSUMED: Automerge convergence and cache == CRDT, not proved
// here), all editor buffers show that text. Note edits change `cur`, so this is applied at the point
// where all edits and all messages (CRDT sync and editor) have been delivered.
pub proof fn theorem_all_editors_agree(w1: W, w2: W)
    requires
        inv(w1), inv(w2), quiescent(w1), quiescent(w2),
        w1.srv.cur == w2.srv.cur,   // ASSUMPTION
    ensures w1.ed.buf == w2.ed.buf, w1.ed.buf == w1.srv.cur,
{
    theorem_quiescent_agreement(w1);
    theorem_quiescent_agreement(w2);
}

// Non-vacuity: a drain from a nonquiescent reachable state really takes steps (the overtaking run).
pub proof fn example_liveness(content: Seq<char>, o1: int, o2: int)
    ensures ({
        let w0 = W { srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
                     ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() };
        let w2 = ed_local(crdt_step(w0, o1), o2);
        inv(w2) && !quiescent(w2)
    }),
{
    lemma_init(content);
    let w0 = W { srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
                 ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() };
    lemma_crdt_step(w0, o1);
    lemma_ed_local(crdt_step(w0, o1), o2);
}

} // verus!
fn main() {}
