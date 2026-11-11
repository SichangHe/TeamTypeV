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
pub uninterp spec fn tgt_len_of(o: int) -> nat;       // length of the result of o on a text of exactly base_len_of(o)

// LENGTH AXIOMS (ASSUMED; facts of the operational-transform crate)
// force_apply keeps the untouched suffix: an op whose base fits the text changes the length by tgt - base
#[verifier::external_body]
pub proof fn axiom_len_ap(d: Seq<char>, o: int)
    requires base_len_of(o) <= d.len(),
    ensures ap(d, o).len() == d.len() - base_len_of(o) + tgt_len_of(o),
{}
// `retain(n)` extends base and target by n
#[verifier::external_body]
pub proof fn axiom_len_pad(o: int, n: nat)
    ensures base_len_of(pad(o, n)) == base_len_of(o) + n, tgt_len_of(pad(o, n)) == tgt_len_of(o) + n,
{}
// transform of two ops with equal base: each result is based on the other's target
#[verifier::external_body]
pub proof fn axiom_len_tr(m: int, t: int)
    requires base_len_of(m) == base_len_of(t),
    ensures base_len_of(tr_their(m, t)) == tgt_len_of(m), base_len_of(tr_my(m, t)) == tgt_len_of(t),
{}

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


// ---------- length-fit invariant (new): every queued op fits the text it is applied to ----------
// `fits(d, o)`: the op's base does not reach past the text (the CRDT/`apply_to` success condition)
pub open spec fn fits(d: Seq<char>, o: int) -> bool { base_len_of(o) <= d.len() }

pub open spec fn fitq(d: Seq<char>, q: Seq<int>) -> bool
    decreases q.len(),
{
    q.len() == 0 || (fits(d, q[0]) && fitq(ap(d, q[0]), q.drop_first()))
}
pub open spec fn wf2(s: Srv) -> bool { wf(s) && fitq(s.lc, s.q) }

pub proof fn lemma_fitq_snoc(d: Seq<char>, q: Seq<int>, x: int)
    requires fitq(d, q), fits(fold(d, q), x),
    ensures fitq(d, q.push(x)),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(q.push(x).drop_first() =~= Seq::<int>::empty());
        assert(q.push(x)[0] == x);
        assert(fold(d, q) == d);
        assert(fitq(ap(d, x), Seq::<int>::empty()));
    } else {
        assert(q.push(x).drop_first() =~= q.drop_first().push(x));
        assert(q.push(x)[0] == q[0]);
        assert(fold(d, q) == fold(ap(d, q[0]), q.drop_first()));
        lemma_fitq_snoc(ap(d, q[0]), q.drop_first(), x);
    }
}

pub proof fn lemma_fitq_split(d: Seq<char>, q: Seq<int>, k: int)
    requires fitq(d, q), 0 <= k <= q.len(),
    ensures fitq(d, q.subrange(0, k)), fitq(fold(d, q.subrange(0, k)), q.subrange(k, q.len() as int)),
    decreases q.len(),
{
    if k == 0 {
        assert(q.subrange(0, 0) =~= Seq::<int>::empty());
        assert(q.subrange(0, q.len() as int) =~= q);
    } else {
        let df = q.drop_first();
        let d1 = ap(d, q[0]);
        lemma_fitq_split(d1, df, k - 1);
        let qk = q.subrange(0, k);
        assert(qk[0] == q[0]);
        assert(qk.drop_first() =~= df.subrange(0, k - 1));
        assert(fold(d, qk) == fold(d1, df.subrange(0, k - 1)));
        assert(q.subrange(k, q.len() as int) =~= df.subrange(k - 1, df.len() as int));
    }
}

// the lengths of the transformed ops fit: tt keeps both the editor op and the queue fitting
pub proof fn lemma_tt_fit(d: Seq<char>, o: int, q: Seq<int>)
    requires fitq(d, q), fits(d, o),
    ensures fitq(ap(d, o), tt(o, q).1), fits(fold(d, q), tt(o, q).0),
    decreases q.len(),
{
    if q.len() > 0 {
        let q0 = q[0];
        let df = q.drop_first();
        let fm = fix_m(q0, o);
        let ft = fix_t(q0, o);
        let o2 = tr_their(fm, ft);
        let my = tr_my(fm, ft);
        let d1 = ap(d, q0);
        axiom_len_ap(d, q0);
        axiom_len_ap(d, o);
        if base_len_of(q0) < base_len_of(o) {
            axiom_len_pad(q0, (base_len_of(o) - base_len_of(q0)) as nat);
        } else {
            axiom_len_pad(o, (base_len_of(q0) - base_len_of(o)) as nat);
        }
        axiom_len_tr(fm, ft);
        axiom_tp1(d, fm, ft);
        lemma_fix(d, q0, o);
        assert(ap(ap(d, o), my) == ap(d1, o2));
        assert(fits(d1, o2));
        assert(fits(ap(d, o), my));
        lemma_tt_fit(d1, o2, df);
        let rest = tt(o2, df).1;
        assert(seq![my].add(rest).drop_first() =~= rest);
        assert(seq![my].add(rest)[0] == my);
    }
}

pub proof fn lemma_crdt_wf2(s: Srv, o: int)
    requires wf2(s), fits(s.cur, o),
    ensures wf2(srv_crdt(s, o).0),
{
    lemma_srv_crdt_wf(s, o);
    lemma_fitq_snoc(s.lc, s.q, o);
}

pub proof fn lemma_edit_wf2(s: Srv, rev: nat, o: int)
    requires
        wf2(s), confirmed(s) <= rev <= s.dr,
        fits(fold(s.lc, s.q.subrange(0, (rev - confirmed(s)) as int)), o),
    ensures
        wf2(srv_edit(s, rev, o).0),
        // the op the CRDT receives fits the text the CRDT holds (= the server's text)
        fits(s.cur, tt(o, s.q.subrange((rev - confirmed(s)) as int, s.q.len() as int)).0),
{
    let k = (rev - confirmed(s)) as int;
    let lc1 = fold(s.lc, s.q.subrange(0, k));
    let q1 = s.q.subrange(k, s.q.len() as int);
    lemma_srv_edit_wf(s, rev, o);
    lemma_fitq_split(s.lc, s.q, k);
    lemma_fold_split(s.lc, s.q, k);
    lemma_tt_fit(lc1, o, q1);
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

// DAEMON CONTRACT (new, ASSUMED): `crdt_ok(d, t)` means the CRDT delta `t` fits text `d`. The daemon
// must only hand `message_from_inside` such deltas; it is the (unproved) obligation of daemon.rs.
pub uninterp spec fn crdt_ok(d: Seq<char>, t: TextDelta) -> bool;
#[verifier::external_body]
pub proof fn axiom_crdt_ok_len(d: Seq<char>, t: TextDelta)
    requires crdt_ok(d, t),
    ensures base_len_of(delta_op(t)) <= d.len(),
{}

pub struct Error;
pub type Result<T> = core::result::Result<T, Error>;

#[verifier::external_body]
pub struct TextDelta { inner: () }
#[verifier::external_body]
pub struct EditorTextDelta { inner: () }
pub uninterp spec fn delta_op(d: TextDelta) -> int;     // the op a TextDelta denotes
pub uninterp spec fn ed_op(d: EditorTextDelta) -> int;  // the op an EditorTextDelta denotes
impl EditorTextDelta {
    #[verifier::external_body]
    pub fn clone(&self) -> (r: Self) ensures r == *self { unimplemented!() }
}
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
    ensures r is Ok ==> ed_op(r->Ok_0) == delta_op(d),
        crdt_ok(content@, d) ==> r is Ok
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
        // ASSUMED: a successful conversion only reads positions inside the content (Position::try_from_offset)
        && base_len_of(delta_op(o->Ok_0.delta)) <= content@.len()
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
            crdt_ok(old(self).current_content@, *delta) ==> r is Ok,
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
            proof { if crdt_ok(old(self).current_content@, *delta) { axiom_crdt_ok_len(old(self).current_content@, *delta); } }
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
            // ... nor the length-fit invariant
            wf2(old(self)@) ==> wf2(final(self)@),
            // a rejected edit never changes the daemon text
            r is Err ==> final(self).current_content@ == old(self).current_content@,
            // an accepted edit is exactly the model's `srv_edit` with the editor's op,
            // and returns the transformed op for the CRDT and the model's batch for the editor
            r is Ok ==> {
                &&& confirmed(old(self)@) <= rev_editor_delta.revision <= old(self).daemon_revision
                // the editor's op fits the confirmed text it was made against
                &&& base_len_of(ed_op(rev_editor_delta.delta)) <=
                        fold(old(self)@.lc, old(self)@.q.subrange(0, (rev_editor_delta.revision - confirmed(old(self)@)) as int)).len()
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
            proof { lemma_wf_er_only(old(self)@, self@); lemma_wf2_er_only(old(self)@, self@); }
            return Err(Error); // bail!
        }

        // The operation might apply to an older daemon revision.
        // We need to transform it through the daemon operations that have happened since then.

        // But we at least we know that the editor has seen all daemon operations until
        // daemon_revision. So we can remove them from the editor queue.
        let daemon_operations_to_transform = self.daemon_revision - daemon_revision;
        if self.editor_queue.len() < daemon_operations_to_transform {
            proof { lemma_wf_er_only(old(self)@, self@); lemma_wf2_er_only(old(self)@, self@); }
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
                    lemma_wf_after_confirm(old(self)@, seen_operations as int, self@); lemma_wf2_after_confirm(old(self)@, seen_operations as int, self@);
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
            if wf2(s0) {
                // `op_seq` fits the confirmed text (try_from_rev_ed_delta), which is `l1`
                assert(l1 == fold(s0.lc, s0.q.subrange(0, k)));
                lemma_edit_wf2(s0, rev_editor_delta.revision as nat, e);
            }
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

pub proof fn lemma_wf2_er_only(s0: Srv, s1: Srv)
    requires s1.dr == s0.dr, s1.q == s0.q, s1.lc == s0.lc, s1.cur == s0.cur,
    ensures wf2(s0) ==> wf2(s1),
{}

pub proof fn lemma_wf2_after_confirm(s0: Srv, k: int, s1: Srv)
    requires wf(s0), 0 <= k <= s0.q.len(), s1.dr == s0.dr,
        s1.q == s0.q.subrange(k, s0.q.len() as int), s1.lc == fold(s0.lc, s0.q.subrange(0, k)), s1.cur == s0.cur,
    ensures wf2(s0) ==> wf2(s1),
{
    lemma_wf_after_confirm(s0, k, s1);
    if wf2(s0) { lemma_fitq_split(s0.lc, s0.q, k); }
}

// =====================================================================================
// EXTENSION: refinement of the real `EditorConnection` (crates/teamtype/src/editor_connection.rs)
// and the message types of editor_protocol.rs. Rewrites vs. the source are listed in DESIGN.md.
// =====================================================================================

// ---------- opaque environment (ASSUMED, all external) ----------
#[verifier::external_body] pub struct RelativePath { inner: () }
impl RelativePath {
    pub uninterp spec fn view(&self) -> int; // injective key of the path (HashMap key identity)
    #[verifier::external_body]
    pub fn clone(&self) -> (r: Self) ensures r@ == self@ { unimplemented!() }
}
#[verifier::external_body] pub struct AbsolutePath { inner: () }
#[verifier::external_body] pub struct AppConfig { inner: () }
impl AppConfig {
    // base_dir is absolute and canonical (main.rs `get_directory` canonicalizes it)
    pub uninterp spec fn base_abs(&self) -> bool;
}
// AppConfig::username (read-only, opaque here: only used as the cursor display name)
#[verifier::external_body]
pub fn clone_username(cfg: &AppConfig) -> (r: Option<String>) { unimplemented!() }
#[verifier::external_body] pub struct ProtoError { inner: () }   // EditorProtocolMessageError
#[verifier::external_body] pub struct Ranges { inner: () }       // Vec<Range>
impl Ranges {
    #[verifier::external_body]
    pub fn clone(&self) -> (r: Self) ensures r == *self { unimplemented!() }
}
pub struct CursorState { pub name: Option<String>, pub file_path: RelativePath, pub ranges: Ranges }

pub enum FromEditor {
    DaemonWriter,
    Save { uri: String },
    Open { uri: String, content: String, saves_file: bool, daemon_writes: bool },
    Close { uri: String },
    Edit { uri: String, revision: usize, delta: EditorTextDelta },
    Cursor { uri: String, ranges: Ranges },
}
pub enum ToEditor {
    Edit { uri: String, revision: usize, delta: EditorTextDelta },
    Cursor { userid: String, name: Option<String>, uri: String, ranges: Ranges },
}
pub enum ComponentMessage {
    Open { file_path: RelativePath, content: String },
    Close { file_path: RelativePath },
    Edit { file_path: RelativePath, delta: TextDelta },
    Cursor { cursor_id: String, cursor_state: CursorState },
}

pub uninterp spec fn uri_of(k: int) -> Seq<char>; // the file:// URI the daemon renders for a path

// FileUri::try_from + to_absolute_path, error mapped to a protocol error. Trusted: Err on a bad
// URI, never panics (the source `.expect`s `Url::parse` on a `file:///` string).
#[verifier::external_body]
pub fn uri_to_abs(uri: &String) -> (r: core::result::Result<AbsolutePath, ProtoError>) { unimplemented!() }
// RelativePath::try_from_absolute, error mapped
#[verifier::external_body]
pub fn relativize(cfg: &AppConfig, p: &AbsolutePath) -> (r: core::result::Result<RelativePath, ProtoError>) { unimplemented!() }
// `AbsolutePath::from_parts(base, rel).expect(..).to_file_uri().to_string()`; cannot fail when the
// base directory is absolute (ASSUMED)
#[verifier::external_body]
pub fn uri_str(cfg: &AppConfig, rel: &RelativePath) -> (r: String)
    requires cfg.base_abs(),
    ensures r@ == uri_of(rel@),
{ unimplemented!() }
// sandbox::exists, error mapped
#[verifier::external_body]
pub fn sandbox_exists(cfg: &AppConfig, p: &AbsolutePath) -> (r: core::result::Result<bool, ProtoError>) { unimplemented!() }
// sandbox::write_file(.., b"") (touches the disk only), error mapped
#[verifier::external_body]
pub fn sandbox_touch(cfg: &AppConfig, p: &AbsolutePath) -> (r: core::result::Result<(), ProtoError>) { unimplemented!() }
// sandbox::ignored, error mapped (source `.expect`ed it: fixed, see DESIGN.md)
#[verifier::external_body]
pub fn sandbox_ignored(cfg: &AppConfig, p: &AbsolutePath) -> (r: core::result::Result<bool, ProtoError>) { unimplemented!() }
// sandbox::read_file then `std::str::from_utf8(..).is_err()`, errors mapped
#[verifier::external_body]
pub fn sandbox_is_utf8(cfg: &AppConfig, p: &AbsolutePath) -> (r: core::result::Result<bool, ProtoError>) { unimplemented!() }
// constructors of fixed protocol errors
#[verifier::external_body]
pub fn err_legacy_open() -> (r: ProtoError) { unimplemented!() }
#[verifier::external_body]
pub fn err_git_running() -> (r: ProtoError) { unimplemented!() }
#[verifier::external_body]
pub fn err_ignored(p: &AbsolutePath) -> (r: ProtoError) { unimplemented!() }
#[verifier::external_body]
pub fn err_not_utf8() -> (r: ProtoError) { unimplemented!() }
#[verifier::external_body]
pub fn err_file_not_found() -> (r: ProtoError) { unimplemented!() }
#[verifier::external_body]
pub fn err_invalid_edit() -> (r: ProtoError) { unimplemented!() }

// `String::clone` (spec not provided by vstd)
#[verifier::external_body]
pub fn clone_str(s: &String) -> (r: String) ensures r@ == s@ { unimplemented!() }

// `.expect(..)` that must not fire; `requires false` makes reaching it a proof obligation
pub fn expect_failed() -> (r: !)
    requires false,
{ unimplemented!() }

// `HashMap<RelativePath, OTServer>` as an abstract finite map from path key to server state.
// `get_mut` is replaced by `take` + `insert` of the same key (see DESIGN.md).
#[verifier::external_body]
pub struct ServerMap { inner: () }
impl ServerMap {
    pub uninterp spec fn view(&self) -> Map<int, Srv>;
    #[verifier::external_body]
    pub fn new() -> (r: Self) ensures r@ == Map::<int, Srv>::empty() { unimplemented!() }
    #[verifier::external_body]
    pub fn contains_key(&self, k: &RelativePath) -> (r: bool) ensures r == self@.contains_key(k@) { unimplemented!() }
    #[verifier::external_body]
    pub fn remove(&mut self, k: &RelativePath) ensures final(self)@ == old(self)@.remove(k@) { unimplemented!() }
    #[verifier::external_body]
    pub fn insert(&mut self, k: RelativePath, v: OTServer) ensures final(self)@ == old(self)@.insert(k@, v@) { unimplemented!() }
    #[verifier::external_body]
    pub fn take(&mut self, k: &RelativePath) -> (r: Option<OTServer>)
        ensures
            final(self)@ == old(self)@.remove(k@),
            match r {
                Some(s) => old(self)@.contains_key(k@) && s@ == old(self)@[k@],
                None => !old(self)@.contains_key(k@),
            },
    { unimplemented!() }
}

pub open spec fn fresh_srv(content: Seq<char>) -> Srv {
    Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content }
}
// every open file's server is well-formed
pub open spec fn map_wf(m: Map<int, Srv>) -> bool {
    forall|k: int| #[trigger] m.contains_key(k) ==> wf(m[k])
}
// counters have headroom (the real code can overflow only after 2^64 messages; ASSUMED away)
pub open spec fn map_room(m: Map<int, Srv>) -> bool {
    forall|k: int| #[trigger] m.contains_key(k) ==> m[k].er < usize::MAX && m[k].dr < usize::MAX
}
// a rejected edit touched at most one server, kept it well-formed with the same text, same daemon
// revision, and only possibly advanced its editor revision / confirmed text
pub open spec fn same_except(old_m: Map<int, Srv>, new_m: Map<int, Srv>, k0: int) -> bool {
    forall|k: int| old_m.contains_key(k) && k != k0 ==> #[trigger] new_m[k] == old_m[k]
}
pub open spec fn err_edit_effect(old_m: Map<int, Srv>, new_m: Map<int, Srv>) -> bool {
    &&& new_m.dom() == old_m.dom()
    &&& exists|k0: int| same_except(old_m, new_m, k0)
    &&& forall|k: int| #[trigger] old_m.contains_key(k) ==> {
        &&& new_m[k].cur == old_m[k].cur && new_m[k].dr == old_m[k].dr
        &&& new_m[k].er <= old_m[k].er + 1 && new_m[k].er >= old_m[k].er
        &&& wf(new_m[k])
        &&& (wf2(old_m[k]) ==> wf2(new_m[k]))
    }
}

pub proof fn lemma_err_effect_refl(m: Map<int, Srv>)
    requires map_wf(m),
    ensures err_edit_effect(m, m),
{
    assert(same_except(m, m, 0));
}

// ---------- the connection ----------
pub struct EditorConnection {
    pub id: String,
    pub app_config: AppConfig,
    pub ot_servers: ServerMap,
    pub username: Option<String>,
}

impl EditorConnection {
    pub open spec fn inv(&self) -> bool {
        self.app_config.base_abs() && map_wf(self.ot_servers@)
    }

    // corr: crates/teamtype/src/editor_connection.rs :: EditorConnection::new
    pub fn new(id: String, app_config: AppConfig) -> (r: Self)
        requires app_config.base_abs(),
        ensures r.inv(), r.ot_servers@ == Map::<int, Srv>::empty(), r.app_config == app_config,
    {
        Self { id, username: clone_username(&app_config), app_config, ot_servers: ServerMap::new() }
    }
    // corr-end

    // corr: crates/teamtype/src/editor_connection.rs :: EditorConnection::owns
    pub fn owns(&self, file_path: &RelativePath) -> (r: bool)
        ensures r == self.ot_servers@.contains_key(file_path@),
    {
        self.ot_servers.contains_key(file_path)
    }
    // corr-end

    // corr: crates/teamtype/src/editor_connection.rs :: EditorConnection::invalidate_file
    pub fn invalidate_file(&mut self, file_path: &RelativePath)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).ot_servers@ == old(self).ot_servers@.remove(file_path@),
            final(self).app_config == old(self).app_config,
    {
        self.ot_servers.remove(file_path);
    }
    // corr-end

    /// Daemon contract (not proved): an Edit for an open file fits that file's server text.
    pub open spec fn inside_ok(&self, m: &ComponentMessage) -> bool {
        match m {
            ComponentMessage::Edit { file_path, delta } =>
                self.ot_servers@.contains_key(file_path@) ==> crdt_ok(self.ot_servers@[file_path@].cur, *delta),
            _ => true,
        }
    }

    // corr: crates/teamtype/src/editor_connection.rs :: EditorConnection::message_from_inside
    pub fn message_from_inside(&mut self, message: &ComponentMessage) -> (r: Vec<ToEditor>)
        requires old(self).inv(), map_room(old(self).ot_servers@), old(self).inside_ok(message),
        ensures
            final(self).inv(),
            final(self).app_config == old(self).app_config,
            // CRDT edit for an open file: exactly the model's `srv_crdt`, one message with its revision/op
            ({ if let ComponentMessage::Edit { file_path, delta } = message {
                if old(self).ot_servers@.contains_key(file_path@) {
                    let (s1, m1) = srv_crdt(old(self).ot_servers@[file_path@], delta_op(*delta));
                    &&& final(self).ot_servers@ == old(self).ot_servers@.insert(file_path@, s1)
                    &&& r@.len() == 1
                    &&& r@[0] is Edit
                    &&& r@[0]->Edit_revision == m1.rev
                    &&& ed_op(r@[0]->Edit_delta) == m1.op
                    &&& r@[0]->Edit_uri@ == uri_of(file_path@)
                } else {
                    // not open: ignored
                    &&& final(self).ot_servers@ == old(self).ot_servers@
                    &&& r@.len() == 0
                }
            } else if let ComponentMessage::Cursor { cursor_id, cursor_state } = message {
                &&& final(self).ot_servers@ == old(self).ot_servers@
                &&& r@.len() == 1
                &&& r@[0] is Cursor
                &&& r@[0]->Cursor_userid@ == cursor_id@
                &&& r@[0]->Cursor_uri@ == uri_of(cursor_state.file_path@)
                &&& r@[0]->Cursor_ranges == cursor_state.ranges
            } else {
                &&& final(self).ot_servers@ == old(self).ot_servers@
                &&& r@.len() == 0
            } }),
    {
        match message {
            ComponentMessage::Edit { file_path, delta } => {
                match self.ot_servers.take(file_path) {
                    Some(mut ot_server) => {
                        let rev_text_delta_for_editor = match ot_server.apply_crdt_change(delta) {
                            Ok(x) => x,
                            Err(_) => expect_failed(),
                        };
                        let uri = uri_str(&self.app_config, file_path);
                        let mut v: Vec<ToEditor> = Vec::new();
                        v.push(ToEditor::Edit {
                            uri,
                            delta: rev_text_delta_for_editor.delta,
                            revision: rev_text_delta_for_editor.revision,
                        });
                        self.ot_servers.insert(file_path.clone(), ot_server);
                        v
                    }
                    None => Vec::new(),
                }
            }
            ComponentMessage::Cursor { cursor_id, cursor_state } => {
                let uri = uri_str(&self.app_config, &cursor_state.file_path);
                let mut v: Vec<ToEditor> = Vec::new();
                v.push(ToEditor::Cursor {
                    userid: clone_str(cursor_id),
                    name: cursor_state.name.clone(),
                    uri,
                    ranges: cursor_state.ranges.clone(),
                });
                v
            }
            _ => Vec::new(),
        }
    }
    // corr-end

    fn resolve(&self, uri: &String) -> (r: core::result::Result<RelativePath, ProtoError>) {
        let absolute_path = match uri_to_abs(uri) { Ok(x) => x, Err(e) => return Err(e) };
        relativize(&self.app_config, &absolute_path)
    }

    // corr: crates/teamtype/src/editor_connection.rs :: EditorConnection::message_from_editor
    pub fn message_from_editor(&mut self, allow_file_creation: bool, message: &FromEditor)
        -> (r: core::result::Result<(ComponentMessage, Vec<ToEditor>), ProtoError>)
        requires
            old(self).inv(), map_room(old(self).ot_servers@),
            // the daemon answers these itself (daemon.rs `react_to_message_from_editor`) and never forwards them
            !(message is DaemonWriter), !(message is Save),
        ensures
            final(self).inv(),
            final(self).app_config == old(self).app_config,
            // no overflow: counters advance by at most one
            (message is Edit || message is Cursor) ==> forall|k: int| #[trigger] old(self).ot_servers@.contains_key(k) && final(self).ot_servers@.contains_key(k)
                ==> final(self).ot_servers@[k].er <= old(self).ot_servers@[k].er + 1
                    && final(self).ot_servers@[k].dr == old(self).ot_servers@[k].dr,
            match message {
                FromEditor::Open { content, saves_file, daemon_writes, .. } => {
                    // legacy plugins are rejected
                    &&& (*saves_file || !*daemon_writes) ==> r is Err
                    // rejection leaves connection state untouched
                    &&& r is Err ==> final(self).ot_servers@ == old(self).ot_servers@
                    // acceptance (re)creates a fresh session for exactly the path it reports
                    &&& r is Ok ==> {
                        let (cm, to_ed) = r->Ok_0;
                        &&& cm is Open
                        &&& cm->Open_content@ == content@
                        &&& to_ed@.len() == 0
                        &&& final(self).ot_servers@ == old(self).ot_servers@.insert(cm->Open_file_path@, fresh_srv(content@))
                        &&& !*saves_file && *daemon_writes
                    }
                },
                FromEditor::Close { .. } => {
                    &&& r is Err ==> final(self).ot_servers@ == old(self).ot_servers@
                    &&& r is Ok ==> {
                        let (cm, to_ed) = r->Ok_0;
                        &&& cm is Close
                        &&& to_ed@.len() == 0
                        &&& final(self).ot_servers@ == old(self).ot_servers@.remove(cm->Close_file_path@)
                        &&& !final(self).ot_servers@.contains_key(cm->Close_file_path@)
                    }
                },
                FromEditor::Edit { revision, delta, .. } => {
                    // a rejected edit never emits anything and never changes any text or daemon revision
                    &&& r is Err ==> err_edit_effect(old(self).ot_servers@, final(self).ot_servers@)
                    &&& r is Ok ==> {
                        let (cm, to_ed) = r->Ok_0;
                        &&& cm is Edit
                        &&& old(self).ot_servers@.contains_key(cm->Edit_file_path@)  // only for open files
                        &&& ({
                            let k = cm->Edit_file_path@;
                            let s0 = old(self).ot_servers@[k];
                            let (s1, batch) = srv_edit(s0, *revision as nat, ed_op(*delta));
                            &&& final(self).ot_servers@ == old(self).ot_servers@.insert(k, s1)
                            &&& confirmed(s0) <= *revision <= s0.dr
                            // the editor's op fits the confirmed text it was made against
                            &&& base_len_of(ed_op(*delta)) <= fold(s0.lc, s0.q.subrange(0, *revision - confirmed(s0))).len()
                            // the CRDT receives the model's transformed op
                            &&& delta_op(cm->Edit_delta) == tt(ed_op(*delta),
                                    s0.q.subrange(*revision - confirmed(s0), s0.q.len() as int)).0
                            // the editor receives the model's batch, to the file's URI
                            &&& to_ed@.len() == batch.len()
                            &&& forall|i: int| 0 <= i < to_ed@.len() ==> {
                                &&& (#[trigger] to_ed@[i]) is Edit
                                &&& to_ed@[i]->Edit_revision == batch[i].rev
                                &&& ed_op(to_ed@[i]->Edit_delta) == batch[i].op
                                &&& to_ed@[i]->Edit_uri@ == uri_of(k)
                            }
                        })
                    }
                },
                FromEditor::Cursor { ranges, .. } => {
                    &&& final(self).ot_servers@ == old(self).ot_servers@
                    &&& r is Ok ==> {
                        let (cm, to_ed) = r->Ok_0;
                        &&& cm is Cursor
                        &&& cm->Cursor_cursor_id@ == old(self).id@
                        &&& cm->Cursor_cursor_state.ranges == *ranges
                        &&& to_ed@.len() == 0
                    }
                },
                _ => true,
            },
    {
        match message {
            FromEditor::Open { uri, content, saves_file, daemon_writes } => {
                if *saves_file || !*daemon_writes {
                    return Err(err_legacy_open());
                }
                let absolute_path = match uri_to_abs(uri) { Ok(x) => x, Err(e) => return Err(e) };
                let relative_path = match relativize(&self.app_config, &absolute_path) {
                    Ok(x) => x, Err(e) => return Err(e),
                };
                let exists = match sandbox_exists(&self.app_config, &absolute_path) {
                    Ok(x) => x, Err(e) => return Err(e),
                };
                if !exists {
                    if !allow_file_creation {
                        return Err(err_git_running());
                    }
                    match sandbox_touch(&self.app_config, &absolute_path) {
                        Ok(()) => {}, Err(e) => return Err(e),
                    }
                }
                let ignored = match sandbox_ignored(&self.app_config, &absolute_path) {
                    Ok(x) => x, Err(e) => return Err(e),
                };
                if ignored {
                    return Err(err_ignored(&absolute_path));
                }
                let utf8 = match sandbox_is_utf8(&self.app_config, &absolute_path) {
                    Ok(x) => x, Err(e) => return Err(e),
                };
                if !utf8 {
                    return Err(err_not_utf8());
                }
                let c = clone_str(content);
                let ot_server = OTServer::new(c);
                proof { assert(ot_server@.q =~= Seq::<int>::empty()); assert(ot_server@ == fresh_srv(content@)); }
                self.ot_servers.insert(relative_path.clone(), ot_server);
                proof { assert(self.ot_servers@ =~= old(self).ot_servers@.insert(relative_path@, fresh_srv(content@))); }
                Ok((ComponentMessage::Open { file_path: relative_path, content: clone_str(content) }, Vec::new()))
            }
            FromEditor::Close { uri } => {
                let relative_path = match self.resolve(uri) { Ok(x) => x, Err(e) => return Err(e) };
                self.ot_servers.remove(&relative_path);
                Ok((ComponentMessage::Close { file_path: relative_path }, Vec::new()))
            }
            FromEditor::Edit { uri, revision, delta } => {
                let relative_path = match self.resolve(uri) {
                    Ok(x) => x,
                    Err(e) => { proof { lemma_err_effect_refl(old(self).ot_servers@); } return Err(e) }
                };
                let mut ot_server = match self.ot_servers.take(&relative_path) {
                    Some(s) => s,
                    None => {
                        proof {
                            assert(self.ot_servers@ =~= old(self).ot_servers@);
                            lemma_err_effect_refl(old(self).ot_servers@);
                        }
                        return Err(err_file_not_found())
                    }
                };
                let rev_delta = RevisionedEditorTextDelta { revision: *revision, delta: delta.clone() };
                let ghost old_map = old(self).ot_servers@;
                let result = ot_server.apply_editor_operation(rev_delta);
                match result {
                    Err(_) => {
                        proof {
                            assert(old_map.contains_key(relative_path@));
                        }
                        self.ot_servers.insert(relative_path.clone(), ot_server);
                        proof {
                            let nm = self.ot_servers@;
                            assert(nm.dom() =~= old_map.dom());
                            assert(same_except(old_map, nm, relative_path@));
                            assert forall|k: int| #[trigger] old_map.contains_key(k) implies {
                                &&& nm[k].cur == old_map[k].cur && nm[k].dr == old_map[k].dr
                                &&& nm[k].er <= old_map[k].er + 1 && nm[k].er >= old_map[k].er
                                &&& wf(nm[k])
                                &&& (wf2(old_map[k]) ==> wf2(nm[k]))
                            } by {
                                if k == relative_path@ { assert(nm[k] == ot_server@); } else { assert(nm[k] == old_map[k]); }
                            }
                            assert(err_edit_effect(old_map, nm));
                        }
                        Err(err_invalid_edit())
                    }
                    Ok((delta_for_crdt, rev_deltas_for_editor)) => {
                        let ghost s0 = old_map[relative_path@];
                        self.ot_servers.insert(relative_path.clone(), ot_server);
                        proof {
                            assert(self.ot_servers@ =~= old_map.insert(relative_path@, srv_edit(s0, *revision as nat, ed_op(*delta)).0));
                        }
                        let uri = uri_str(&self.app_config, &relative_path);
                        let mut messages_to_editor: Vec<ToEditor> = Vec::new();
                        let mut i: usize = 0;
                        while i < rev_deltas_for_editor.len()
                            invariant
                                i <= rev_deltas_for_editor@.len(),
                                messages_to_editor@.len() == i,
                                forall|j: int| 0 <= j < i ==> {
                                    &&& (#[trigger] messages_to_editor@[j]) is Edit
                                    &&& messages_to_editor@[j]->Edit_revision == rev_deltas_for_editor@[j].revision
                                    &&& ed_op(messages_to_editor@[j]->Edit_delta) == ed_op(rev_deltas_for_editor@[j].delta)
                                    &&& messages_to_editor@[j]->Edit_uri@ == uri@
                                },
                            decreases rev_deltas_for_editor@.len() - i,
                        {
                            let d = &rev_deltas_for_editor[i];
                            messages_to_editor.push(ToEditor::Edit {
                                uri: clone_str(&uri),
                                delta: d.delta.clone(),
                                revision: d.revision,
                            });
                            i += 1;
                        }
                        proof {
                            let s1 = srv_edit(s0, *revision as nat, ed_op(*delta)).0;
                            let b = srv_edit(s0, *revision as nat, ed_op(*delta)).1;
                            lemma_batch(s1.q, s1.er, *revision as nat);
                            assert(b == batch(s1.q, s1.er, *revision as nat));
                            assert(s1 == self.ot_servers@[relative_path@]);
                        }
                        Ok((ComponentMessage::Edit { file_path: relative_path, delta: delta_for_crdt }, messages_to_editor))
                    }
                }
            }
            FromEditor::Cursor { uri, ranges } => {
                let relative_path = match self.resolve(uri) { Ok(x) => x, Err(e) => return Err(e) };
                Ok((ComponentMessage::Cursor {
                    cursor_id: clone_str(&self.id),
                    cursor_state: CursorState {
                        name: self.username.clone(),
                        file_path: relative_path,
                        ranges: ranges.clone(),
                    },
                }, Vec::new()))
            }
            FromEditor::DaemonWriter | FromEditor::Save { .. } => {
                expect_failed()
            }
        }
    }
    // corr-end
}

// =====================================================================================
// DAEMON MODEL (new). An abstract state machine of crates/teamtype/src/daemon.rs + document.rs, restricted to
// what decides whether `EditorConnection::message_from_inside` is only ever called with an Edit that fits the
// connection's server text (`inside_ok`). It is NOT a refinement of the Rust: each `Step` below is a hand-written
// abstraction of the code paths named in its comment; the mapping is a claim checked by reading (see STATUS.md).
// The editor side IS refined: `message_from_inside`/`message_from_editor` (above) match `srv_crdt`/`srv_edit`.
// =====================================================================================

// ASSUMED: the CRDT/`apply_to` success condition for a delta is exactly that it does not reach past the text
// (TextDelta::apply_to bails on Retain/Delete past the end; Position::try_from_offset likewise).
#[verifier::external_body]
pub proof fn axiom_crdt_ok_iff(d: Seq<char>, t: TextDelta)
    ensures crdt_ok(d, t) <==> fits(d, delta_op(t)),
{}

// `TextDelta::delete(n)` on a text of exactly n chars empties it (the "peer deleted your open file" delta)
pub uninterp spec fn del_all(n: nat) -> int;
#[verifier::external_body]
pub proof fn axiom_del_all(d: Seq<char>)
    ensures base_len_of(del_all(d.len())) == d.len(), ap(d, del_all(d.len())) == Seq::<char>::empty(),
{}

// bridge to the real contract: the model's `fits` is the real `inside_ok` for a CRDT Edit
pub proof fn lemma_inside_ok_bridge(ec: &EditorConnection, f: RelativePath, delta: TextDelta)
    requires ec.ot_servers@.contains_key(f@) ==> fits(ec.ot_servers@[f@].cur, delta_op(delta)),
    ensures ec.inside_ok(&ComponentMessage::Edit { file_path: f, delta }),
{
    if ec.ot_servers@.contains_key(f@) { axiom_crdt_ok_iff(ec.ot_servers@[f@].cur, delta); }
}

pub enum DocContent { Text(Seq<char>), Bytes }

// doc: the shared document per file (absent = no such file); eds: per editor connection, per open file, the
// OTServer state (an editor with a file open owns a server); pend: edits already in the document that have not yet
// been broadcast to the editors (daemon.rs `disk_edits`, and sync patches before `broadcast_to_editors`).
pub struct DState {
    pub doc: Map<int, DocContent>,
    pub eds: Map<int, Map<int, Srv>>,
    pub pend: Map<int, Seq<int>>,
}

pub open spec fn pq(st: DState, f: int) -> Seq<int> { if st.pend.contains_key(f) { st.pend[f] } else { Seq::empty() } }
pub open spec fn is_open(st: DState, e: int, f: int) -> bool { st.eds.contains_key(e) && st.eds[e].contains_key(f) }
pub open spec fn is_text(st: DState, f: int) -> bool { st.doc.contains_key(f) && st.doc[f] is Text }
pub open spec fn doc_text(st: DState, f: int) -> Seq<char> {
    if st.doc.contains_key(f) { match st.doc[f] { DocContent::Text(t) => t, DocContent::Bytes => Seq::empty() } } else { Seq::empty() }
}
pub open spec fn all_drained(st: DState) -> bool { forall|f: int| #[trigger] pq(st, f).len() == 0 }

// THE INVARIANT. For every editor e with file f open:
//  (1) its server is well-formed and every queued op fits;
//  (2) the document holds f as text, and the server's text plus the not-yet-broadcast edits is the document text
//      (so when nothing is pending, server text == document text);
//  (3) all editors with f open agree on the server text.
pub open spec fn dinv(st: DState) -> bool {
    &&& forall|e: int, f: int| #[trigger] is_open(st, e, f) ==> wf2(st.eds[e][f])
    &&& forall|e: int, f: int| #[trigger] is_open(st, e, f) ==> {
        &&& is_text(st, f)
        &&& fold(st.eds[e][f].cur, pq(st, f)) == doc_text(st, f)
        &&& fitq(st.eds[e][f].cur, pq(st, f))
    }
    &&& forall|e: int, e2: int, f: int| #[trigger] is_open(st, e, f) && #[trigger] is_open(st, e2, f)
            ==> st.eds[e][f].cur == st.eds[e2][f].cur
}

pub enum Step {
    // doc text changed by a disk write merged by `merge_disk_content`/`update_text`, or by a peer's sync patch
    // (FileChange). The delta is queued. Requires the delta fits the current doc text (the code `expect`s it).
    DocEdit { f: int, o: int },
    // sync patch FileRemoval for a file some editor has open (daemon.rs ReceiveSyncMessage, "not owned" branch):
    // earlier queued deltas of this sync for f are dropped, a delete-all of the text before the sync is queued,
    // the document file becomes the empty text. `c` is `file_content_at(.., heads_before_sync_message)`.
    SyncRemoval { f: int, before: Seq<char> },
    // text -> binary (merge_disk_content non-UTF-8 branch, patch FileBytes): `invalidate_editor_file` then doc := Bytes
    Invalidate { f: int },
    // doc change of a file no editor has open: removal (`remove_file` when `owns`), set_file, binary, empty text...
    FreeDoc { f: int, nc: Option<DocContent> },
    // `send_disk_edits` / `broadcast_to_editors(None, Edit)`: the oldest queued edit of f goes to every editor
    Drain { f: int },
    // `react_to_message_from_editor` with an accepted Edit: `message_from_editor` on e's connection, then
    // `process_component_message(Some(e), Edit)` applies the transformed op to the CRDT and broadcasts it to others
    EditorEdit { e: int, f: int, rev: nat, o: int },
    // a rejected Edit: only e's server bookkeeping changes (no text, no doc)
    EditorReject { e: int, f: int, s2: Srv },
    // accepted Open: a fresh server with the editor's content c; then `process_component_message(Open)`:
    // doc has text -> e's server gets the diff edit `d` (None when equal) via `process_in_editor`; otherwise
    // the document takes c (`set_file`)
    EditorOpen { e: int, f: int, c: Seq<char>, d: Option<int> },
    EditorClose { e: int, f: int },
    NewConn { e: int },
    CloseConn { e: int },
}

pub open spec fn k_of(s: Srv, rev: nat) -> int { (rev - confirmed(s)) as int }
pub open spec fn lc1_of(s: Srv, rev: nat) -> Seq<char> { fold(s.lc, s.q.subrange(0, k_of(s, rev))) }
pub open spec fn q1_of(s: Srv, rev: nat) -> Seq<int> { s.q.subrange(k_of(s, rev), s.q.len() as int) }
// the op the CRDT receives for an accepted editor edit
pub open spec fn crdt_op_of(s: Srv, rev: nat, o: int) -> int { tt(o, q1_of(s, rev)).0 }

pub open spec fn step_ok(st: DState, step: Step) -> bool {
    match step {
        Step::DocEdit { f, o } => is_text(st, f) && fits(doc_text(st, f), o),
        Step::SyncRemoval { f, before } => forall|e: int| #[trigger] is_open(st, e, f) ==> st.eds[e][f].cur == before,
        Step::Invalidate { f } => true,
        Step::FreeDoc { f, nc } => forall|e: int| !(#[trigger] is_open(st, e, f)),
        Step::Drain { f } => pq(st, f).len() > 0,
        Step::EditorEdit { e, f, rev, o } => {
            &&& all_drained(st)
            &&& is_open(st, e, f)
            &&& confirmed(st.eds[e][f]) <= rev <= st.eds[e][f].dr
            // `message_from_editor` accepted: the editor's op fits the confirmed text (see its ensures)
            &&& fits(lc1_of(st.eds[e][f], rev), o)
        },
        Step::EditorReject { e, f, s2 } => is_open(st, e, f) && s2.cur == st.eds[e][f].cur && wf2(s2),
        Step::EditorOpen { e, f, c, d } => {
            &&& all_drained(st)
            &&& st.eds.contains_key(e)
            // the diff of editor content against the document text (dissimilar::diff, ASSUMED correct)
            &&& (is_text(st, f) ==> match d {
                None => c == doc_text(st, f),
                Some(dd) => fits(c, dd) && ap(c, dd) == doc_text(st, f),
            })
        },
        Step::EditorClose { e, f } => true,
        Step::NewConn { e } => true,
        Step::CloseConn { e } => true,
    }
}

pub open spec fn upd_eds(st: DState, f: int, g: spec_fn(Srv) -> Srv) -> Map<int, Map<int, Srv>> {
    Map::new(
        st.eds.dom(),
        |e: int| if st.eds[e].contains_key(f) { st.eds[e].insert(f, g(st.eds[e][f])) } else { st.eds[e] },
    )
}

pub open spec fn dapply(st: DState, step: Step) -> DState {
    match step {
        Step::DocEdit { f, o } => DState {
            doc: st.doc.insert(f, DocContent::Text(ap(doc_text(st, f), o))),
            pend: st.pend.insert(f, pq(st, f).push(o)),
            ..st
        },
        Step::SyncRemoval { f, before } => DState {
            doc: st.doc.insert(f, DocContent::Text(Seq::empty())),
            pend: st.pend.insert(f, seq![del_all(before.len())]),
            ..st
        },
        Step::Invalidate { f } => DState {
            doc: st.doc.insert(f, DocContent::Bytes),
            eds: Map::new(st.eds.dom(), |e: int| st.eds[e].remove(f)),
            ..st
        },
        Step::FreeDoc { f, nc } => DState {
            doc: match nc { Some(x) => st.doc.insert(f, x), None => st.doc.remove(f) },
            ..st
        },
        Step::Drain { f } => {
            let o = pq(st, f)[0];
            DState {
                eds: upd_eds(st, f, |s: Srv| srv_crdt(s, o).0),
                pend: st.pend.insert(f, pq(st, f).drop_first()),
                ..st
            }
        }
        Step::EditorEdit { e, f, rev, o } => {
            let s0 = st.eds[e][f];
            let o2 = crdt_op_of(s0, rev, o);
            DState {
                doc: st.doc.insert(f, DocContent::Text(ap(doc_text(st, f), o2))),
                eds: Map::new(
                    st.eds.dom(),
                    |e2: int| if e2 == e { st.eds[e2].insert(f, srv_edit(s0, rev, o).0) }
                        else if st.eds[e2].contains_key(f) { st.eds[e2].insert(f, srv_crdt(st.eds[e2][f], o2).0) }
                        else { st.eds[e2] },
                ),
                ..st
            }
        }
        Step::EditorReject { e, f, s2 } => DState {
            eds: st.eds.insert(e, st.eds[e].insert(f, s2)),
            ..st
        },
        Step::EditorOpen { e, f, c, d } => {
            let s = if is_text(st, f) { match d { Some(dd) => srv_crdt(fresh_srv(c), dd).0, None => fresh_srv(c) } } else { fresh_srv(c) };
            DState {
                doc: if is_text(st, f) { st.doc } else { st.doc.insert(f, DocContent::Text(c)) },
                eds: st.eds.insert(e, st.eds[e].insert(f, s)),
                ..st
            }
        }
        Step::EditorClose { e, f } => DState {
            eds: if st.eds.contains_key(e) { st.eds.insert(e, st.eds[e].remove(f)) } else { st.eds },
            ..st
        },
        Step::NewConn { e } => DState { eds: st.eds.insert(e, Map::empty()), ..st },
        Step::CloseConn { e } => DState { eds: st.eds.remove(e), ..st },
    }
}

// Every Edit that a step hands to `message_from_inside` of some connection, as (editor, file, op): it must fit
// that connection's server text at that moment (this is `inside_ok`), and the document must accept it.
pub open spec fn inside_fits(st: DState, step: Step) -> bool {
    match step {
        Step::Drain { f } => forall|e: int| #[trigger] is_open(st, e, f) ==> fits(st.eds[e][f].cur, pq(st, f)[0]),
        Step::EditorEdit { e, f, rev, o } => {
            let o2 = crdt_op_of(st.eds[e][f], rev, o);
            &&& fits(doc_text(st, f), o2)   // the CRDT apply `expect` (apply_delta_to_doc) cannot fail
            &&& forall|e2: int| e2 != e && #[trigger] is_open(st, e2, f) ==> fits(st.eds[e2][f].cur, o2)
        }
        Step::EditorOpen { e, f, c, d } => is_text(st, f) ==> match d { Some(dd) => fits(c, dd), None => true },
        _ => true,
    }
}

// the I-clauses for st2, given a per-(e,g) justification
pub proof fn lemma_step(st: DState, step: Step)
    requires dinv(st), step_ok(st, step),
    ensures dinv(dapply(st, step)), inside_fits(st, step),
{
    let st2 = dapply(st, step);
    match step {
        Step::DocEdit { f, o } => {
            assert forall|e: int, g: int| #[trigger] is_open(st2, e, g) implies {
                &&& wf2(st2.eds[e][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e][g].cur, pq(st2, g))
            } by {
                assert(is_open(st, e, g));
                if g == f {
                    let s = st.eds[e][f];
                    lemma_fold_snoc(s.cur, pq(st, f), o);
                    lemma_fitq_snoc(s.cur, pq(st, f), o);
                }
            }
            assert forall|e: int, e2: int, g: int| #[trigger] is_open(st2, e, g) && #[trigger] is_open(st2, e2, g)
                implies st2.eds[e][g].cur == st2.eds[e2][g].cur by { assert(is_open(st, e, g) && is_open(st, e2, g)); }
        }
        Step::SyncRemoval { f, before } => {
            assert forall|e: int, g: int| #[trigger] is_open(st2, e, g) implies {
                &&& wf2(st2.eds[e][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e][g].cur, pq(st2, g))
            } by {
                assert(is_open(st, e, g));
                if g == f {
                    let s = st.eds[e][f];
                    assert(s.cur == before);
                    axiom_del_all(before);
                    assert(pq(st2, f) == seq![del_all(before.len())]);
                    assert(pq(st2, f).drop_first() =~= Seq::<int>::empty());
                    assert(fold(s.cur, pq(st2, f)) == fold(ap(s.cur, del_all(before.len())), Seq::<int>::empty()));
                    assert(fitq(ap(s.cur, del_all(before.len())), Seq::<int>::empty()));
                }
            }
            assert forall|e: int, e2: int, g: int| #[trigger] is_open(st2, e, g) && #[trigger] is_open(st2, e2, g)
                implies st2.eds[e][g].cur == st2.eds[e2][g].cur by { assert(is_open(st, e, g) && is_open(st, e2, g)); }
        }
        Step::Invalidate { f } => {
            assert forall|e: int, g: int| #[trigger] is_open(st2, e, g) implies {
                &&& wf2(st2.eds[e][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e][g].cur, pq(st2, g))
            } by {
                assert(is_open(st, e, g));
                assert(g != f);
            }
            assert forall|e: int, e2: int, g: int| #[trigger] is_open(st2, e, g) && #[trigger] is_open(st2, e2, g)
                implies st2.eds[e][g].cur == st2.eds[e2][g].cur by { assert(is_open(st, e, g) && is_open(st, e2, g)); }
        }
        Step::FreeDoc { f, nc } => {
            assert forall|e: int, g: int| #[trigger] is_open(st2, e, g) implies {
                &&& wf2(st2.eds[e][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e][g].cur, pq(st2, g))
            } by {
                assert(is_open(st, e, g));
                assert(g != f);
            }
            assert forall|e: int, e2: int, g: int| #[trigger] is_open(st2, e, g) && #[trigger] is_open(st2, e2, g)
                implies st2.eds[e][g].cur == st2.eds[e2][g].cur by { assert(is_open(st, e, g) && is_open(st, e2, g)); }
        }
        Step::Drain { f } => {
            let o = pq(st, f)[0];
            assert forall|e: int| #[trigger] is_open(st, e, f) implies fits(st.eds[e][f].cur, o) by {
                assert(fitq(st.eds[e][f].cur, pq(st, f)));
            }
            assert forall|e: int, g: int| #[trigger] is_open(st2, e, g) implies {
                &&& wf2(st2.eds[e][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e][g].cur, pq(st2, g))
            } by {
                assert(is_open(st, e, g));
                if g == f {
                    let s = st.eds[e][f];
                    assert(fitq(s.cur, pq(st, f)));
                    lemma_crdt_wf2(s, o);
                    assert(st2.eds[e][f] == srv_crdt(s, o).0);
                    assert(srv_crdt(s, o).0.cur == ap(s.cur, o));
                    assert(fold(s.cur, pq(st, f)) == fold(ap(s.cur, o), pq(st, f).drop_first()));
                } else {
                    assert(st2.eds[e][g] == st.eds[e][g]);
                }
            }
            assert forall|e: int, e2: int, g: int| #[trigger] is_open(st2, e, g) && #[trigger] is_open(st2, e2, g)
                implies st2.eds[e][g].cur == st2.eds[e2][g].cur by {
                assert(is_open(st, e, g) && is_open(st, e2, g));
                if g == f { assert(st.eds[e][f].cur == st.eds[e2][f].cur); }
            }
        }
        Step::EditorEdit { e, f, rev, o } => {
            let s0 = st.eds[e][f];
            let o2 = crdt_op_of(s0, rev, o);
            assert(pq(st, f).len() == 0);
            assert(fold(s0.cur, pq(st, f)) == s0.cur);
            assert(doc_text(st, f) == s0.cur);
            lemma_edit_wf2(s0, rev, o);
            assert(fits(s0.cur, o2));
            assert forall|e2: int| e2 != e && #[trigger] is_open(st, e2, f) implies fits(st.eds[e2][f].cur, o2) by {
                assert(st.eds[e2][f].cur == s0.cur);
            }
            assert forall|e2: int, g: int| #[trigger] is_open(st2, e2, g) implies {
                &&& wf2(st2.eds[e2][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e2][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e2][g].cur, pq(st2, g))
            } by {
                assert(is_open(st, e2, g));
                assert(pq(st2, g).len() == 0);
                if g == f {
                    if e2 == e {
                        assert(st2.eds[e2][g] == srv_edit(s0, rev, o).0);
                    } else {
                        let s2 = st.eds[e2][f];
                        assert(s2.cur == s0.cur);
                        lemma_crdt_wf2(s2, o2);
                        assert(st2.eds[e2][g] == srv_crdt(s2, o2).0);
                    }
                    assert(fitq(st2.eds[e2][g].cur, Seq::<int>::empty()));
                } else {
                    assert(st2.eds[e2][g] == st.eds[e2][g]);
                    assert(fitq(st2.eds[e2][g].cur, Seq::<int>::empty()));
                }
            }
            assert forall|e2: int, e3: int, g: int| #[trigger] is_open(st2, e2, g) && #[trigger] is_open(st2, e3, g)
                implies st2.eds[e2][g].cur == st2.eds[e3][g].cur by {
                assert(is_open(st, e2, g) && is_open(st, e3, g));
                if g == f {
                    assert(st.eds[e2][f].cur == s0.cur);
                    assert(st.eds[e3][f].cur == s0.cur);
                }
            }
        }
        Step::EditorReject { e, f, s2 } => {
            assert forall|e2: int, g: int| #[trigger] is_open(st2, e2, g) implies {
                &&& wf2(st2.eds[e2][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e2][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e2][g].cur, pq(st2, g))
            } by {
                assert(is_open(st, e2, g));
                if e2 == e && g == f {
                    assert(st2.eds[e2][g] == s2);
                    assert(s2.cur == st.eds[e][f].cur);
                    assert(fitq(st.eds[e][f].cur, pq(st, f)));
                } else {
                    assert(st2.eds[e2][g] == st.eds[e2][g]);
                }
            }
            assert forall|e2: int, e3: int, g: int| #[trigger] is_open(st2, e2, g) && #[trigger] is_open(st2, e3, g)
                implies st2.eds[e2][g].cur == st2.eds[e3][g].cur by {
                assert(is_open(st, e2, g) && is_open(st, e3, g));
                if e2 == e && g == f { assert(st2.eds[e2][g] == s2); }
                if e3 == e && g == f { assert(st2.eds[e3][g] == s2); }
            }
        }
        Step::EditorOpen { e, f, c, d } => {
            let sn = if is_text(st, f) { match d { Some(dd) => srv_crdt(fresh_srv(c), dd).0, None => fresh_srv(c) } } else { fresh_srv(c) };
            let fr = fresh_srv(c);
            assert(fr.q =~= Seq::<int>::empty());
            assert(wf2(fr));
            if is_text(st, f) {
                if let Some(dd) = d { lemma_crdt_wf2(fr, dd); }
            }
            assert(wf2(sn));
            assert(sn.cur == doc_text(st, f) || !is_text(st, f));
            assert(sn.cur == c || is_text(st, f));
            assert(st2.doc.contains_key(f) && st2.doc[f] is Text);
            assert(doc_text(st2, f) == sn.cur);
            assert(sn.q.len() == 0 || is_text(st, f));
            assert forall|g: int| #[trigger] pq(st2, g).len() == 0 by { assert(pq(st, g).len() == 0); }
            assert forall|e2: int, g: int| #[trigger] is_open(st2, e2, g) implies {
                &&& wf2(st2.eds[e2][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e2][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e2][g].cur, pq(st2, g))
            } by {
                if e2 == e && g == f {
                    assert(st2.eds[e2][g] == sn);
                    assert(fitq(sn.cur, Seq::<int>::empty()));
                } else {
                    assert(is_open(st, e2, g));
                    if g == f { assert(is_text(st, f)); }
                    assert(st2.eds[e2][g] == st.eds[e2][g]);
                    assert(is_text(st2, g));
                    assert(doc_text(st2, g) == doc_text(st, g));
                }
            }
            assert forall|e2: int, e3: int, g: int| #[trigger] is_open(st2, e2, g) && #[trigger] is_open(st2, e3, g)
                implies st2.eds[e2][g].cur == st2.eds[e3][g].cur by {
                if g == f {
                    if e2 != e { assert(is_open(st, e2, f)); assert(is_text(st, f)); assert(st.eds[e2][f].cur == doc_text(st, f)); }
                    if e3 != e { assert(is_open(st, e3, f)); assert(is_text(st, f)); assert(st.eds[e3][f].cur == doc_text(st, f)); }
                    if e2 == e { assert(st2.eds[e2][g] == sn); }
                    if e3 == e { assert(st2.eds[e3][g] == sn); }
                } else {
                    assert(is_open(st, e2, g) && is_open(st, e3, g));
                }
            }
        }
        Step::EditorClose { e, f } => {
            assert forall|e2: int, g: int| #[trigger] is_open(st2, e2, g) implies {
                &&& wf2(st2.eds[e2][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e2][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e2][g].cur, pq(st2, g))
            } by { assert(is_open(st, e2, g)); }
            assert forall|e2: int, e3: int, g: int| #[trigger] is_open(st2, e2, g) && #[trigger] is_open(st2, e3, g)
                implies st2.eds[e2][g].cur == st2.eds[e3][g].cur by { assert(is_open(st, e2, g) && is_open(st, e3, g)); }
        }
        Step::NewConn { e } => {
            assert forall|e2: int, g: int| #[trigger] is_open(st2, e2, g) implies {
                &&& wf2(st2.eds[e2][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e2][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e2][g].cur, pq(st2, g))
            } by { assert(is_open(st, e2, g)); }
            assert forall|e2: int, e3: int, g: int| #[trigger] is_open(st2, e2, g) && #[trigger] is_open(st2, e3, g)
                implies st2.eds[e2][g].cur == st2.eds[e3][g].cur by { assert(is_open(st, e2, g) && is_open(st, e3, g)); }
        }
        Step::CloseConn { e } => {
            assert forall|e2: int, g: int| #[trigger] is_open(st2, e2, g) implies {
                &&& wf2(st2.eds[e2][g])
                &&& is_text(st2, g)
                &&& fold(st2.eds[e2][g].cur, pq(st2, g)) == doc_text(st2, g)
                &&& fitq(st2.eds[e2][g].cur, pq(st2, g))
            } by { assert(is_open(st, e2, g)); }
            assert forall|e2: int, e3: int, g: int| #[trigger] is_open(st2, e2, g) && #[trigger] is_open(st2, e3, g)
                implies st2.eds[e2][g].cur == st2.eds[e3][g].cur by { assert(is_open(st, e2, g) && is_open(st, e3, g)); }
        }
    }
}

// ---------- headline results ----------
pub open spec fn empty_state() -> DState { DState { doc: Map::empty(), eds: Map::empty(), pend: Map::empty() } }

pub proof fn lemma_dinit()
    ensures dinv(empty_state()),
{
    let st = empty_state();
    assert forall|e: int, f: int| !is_open(st, e, f) by {}
}

// any interleaving of steps, by any number of editors, keeps the invariant and never hands an editor
// connection an edit that does not fit
pub open spec fn run(st: DState, steps: Seq<Step>) -> DState
    decreases steps.len(),
{
    if steps.len() == 0 { st } else { run(dapply(st, steps[0]), steps.drop_first()) }
}
pub open spec fn trace_ok(st: DState, steps: Seq<Step>) -> bool
    decreases steps.len(),
{
    steps.len() == 0 || (step_ok(st, steps[0]) && trace_ok(dapply(st, steps[0]), steps.drop_first()))
}
pub open spec fn trace_inside_fits(st: DState, steps: Seq<Step>) -> bool
    decreases steps.len(),
{
    steps.len() == 0 || (inside_fits(st, steps[0]) && trace_inside_fits(dapply(st, steps[0]), steps.drop_first()))
}

pub proof fn theorem_trace(st: DState, steps: Seq<Step>)
    requires dinv(st), trace_ok(st, steps),
    ensures dinv(run(st, steps)), trace_inside_fits(st, steps),
    decreases steps.len(),
{
    if steps.len() > 0 {
        lemma_step(st, steps[0]);
        theorem_trace(dapply(st, steps[0]), steps.drop_first());
    }
}

// `inside_ok` for the real EditorConnection: when a step broadcasts an edit (Drain, or the CRDT op of an accepted
// editor edit), every other connection `ec` whose servers are the model's satisfies the real contract.
pub proof fn theorem_inside_ok_drain(st: DState, f: int, e: int, ec: &EditorConnection, fp: RelativePath, delta: TextDelta)
    requires
        dinv(st), step_ok(st, Step::Drain { f }),
        ec.ot_servers@ == (if st.eds.contains_key(e) { st.eds[e] } else { Map::<int, Srv>::empty() }),
        fp@ == f, delta_op(delta) == pq(st, f)[0],
    ensures ec.inside_ok(&ComponentMessage::Edit { file_path: fp, delta }),
{
    lemma_step(st, Step::Drain { f });
    if ec.ot_servers@.contains_key(f) { assert(is_open(st, e, f)); }
    lemma_inside_ok_bridge(ec, fp, delta);
}

pub proof fn theorem_inside_ok_editor_edit(st: DState, e: int, f: int, rev: nat, o: int, e2: int,
    ec: &EditorConnection, fp: RelativePath, delta: TextDelta)
    requires
        dinv(st), step_ok(st, Step::EditorEdit { e, f, rev, o }), e2 != e,
        ec.ot_servers@ == (if st.eds.contains_key(e2) { st.eds[e2] } else { Map::<int, Srv>::empty() }),
        fp@ == f, delta_op(delta) == crdt_op_of(st.eds[e][f], rev, o),
    ensures ec.inside_ok(&ComponentMessage::Edit { file_path: fp, delta }),
{
    lemma_step(st, Step::EditorEdit { e, f, rev, o });
    if ec.ot_servers@.contains_key(f) { assert(is_open(st, e2, f)); }
    lemma_inside_ok_bridge(ec, fp, delta);
}

// quiescence: with nothing pending, every open server holds exactly the document text (so all editors agree)
pub proof fn theorem_quiescent_consistency(st: DState, e: int, f: int)
    requires dinv(st), all_drained(st), is_open(st, e, f),
    ensures is_text(st, f), st.eds[e][f].cur == doc_text(st, f),
{
    assert(pq(st, f).len() == 0);
    assert(fold(st.eds[e][f].cur, pq(st, f)) == st.eds[e][f].cur);
}

// NON-VACUITY: two editors open the same file, one edits, the other receives the edit through
// `srv_crdt` (daemon revision 1), all steps satisfy their preconditions, the end state is consistent.
pub proof fn example_two_editors(f: int, o: int)
    requires base_len_of(o) == 0,
{
    let st0 = empty_state();
    let st1 = dapply(st0, Step::NewConn { e: 1 });
    let st2 = dapply(st1, Step::NewConn { e: 2 });
    let st3 = dapply(st2, Step::FreeDoc { f, nc: Some(DocContent::Text(Seq::empty())) });
    let st4 = dapply(st3, Step::EditorOpen { e: 1, f, c: Seq::empty(), d: None });
    let st5 = dapply(st4, Step::EditorOpen { e: 2, f, c: Seq::empty(), d: None });
    let ed = Step::EditorEdit { e: 1, f, rev: 0, o };
    assert(st2.eds.contains_key(1) && st2.eds.contains_key(2));
    assert(st3.eds == st2.eds);
    assert(is_text(st3, f) && doc_text(st3, f) == Seq::<char>::empty());
    assert(step_ok(st2, Step::FreeDoc { f, nc: Some(DocContent::Text(Seq::empty())) })) by {
        assert forall|e: int| !(#[trigger] is_open(st2, e, f)) by {}
    }
    assert(all_drained(st3)) by { assert forall|g: int| #[trigger] pq(st3, g).len() == 0 by {} }
    assert(step_ok(st3, Step::EditorOpen { e: 1, f, c: Seq::empty(), d: None }));
    assert(all_drained(st4)) by { assert forall|g: int| #[trigger] pq(st4, g).len() == 0 by {} }
    assert(step_ok(st4, Step::EditorOpen { e: 2, f, c: Seq::empty(), d: None }));
    assert(all_drained(st5)) by { assert forall|g: int| #[trigger] pq(st5, g).len() == 0 by {} }
    assert(is_open(st5, 1, f) && is_open(st5, 2, f));
    let s1 = st5.eds[1][f];
    assert(s1 == fresh_srv(Seq::empty()));
    assert(confirmed(s1) == 0);
    assert(lc1_of(s1, 0) == Seq::<char>::empty()) by {
        assert(s1.q.subrange(0, 0) =~= Seq::<int>::empty());
    }
    assert(step_ok(st5, ed));
    let st6 = dapply(st5, ed);
    let o2 = crdt_op_of(s1, 0, o);
    assert(st6.eds[1][f] == srv_edit(s1, 0, o).0);
    assert(st6.eds[2][f] == srv_crdt(st5.eds[2][f], o2).0);
    assert(is_open(st6, 1, f) && is_open(st6, 2, f));
    assert(st6.eds[1][f].er == 1 && st6.eds[1][f].dr == 0);
    assert(st6.eds[2][f].dr == 1 && st6.eds[2][f].er == 0);
    assert(st6.eds[1][f].cur == st6.eds[2][f].cur);
    assert(doc_text(st6, f) == st6.eds[1][f].cur);
}

} // verus!
fn main() {}
