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
// EXTENSION 1: validity ("every op fits its text"), editor rejection.
// Everything above is the single-editor proof, unchanged. New trusted facts are the axioms below.
// =====================================================================================

// fits(d, o): op `o` is applicable to text `d` (base_len(o) <= len(d); for editor deltas: every
// (line, char) position exists in `d`). The real code returns Err / panics otherwise.
pub uninterp spec fn fits(d: Seq<char>, o: int) -> bool;
pub uninterp spec fn idop() -> int;                       // op of the empty editor delta
pub uninterp spec fn diff_op(a: Seq<char>, b: Seq<char>) -> int; // op of `dissimilar::diff(a, b)` (daemon `Open`)

// the empty delta is the identity and fits everything (ASSUMED: `try_from_rev_ed_delta` of `[]`)
#[verifier::external_body]
pub proof fn axiom_id(d: Seq<char>)
    ensures fits(d, idop()), ap(d, idop()) == d,
{}

// the diff op turns a into b (ASSUMED: `dissimilar::diff` is a correct diff and conversions keep it)
#[verifier::external_body]
pub proof fn axiom_diff(a: Seq<char>, b: Seq<char>)
    ensures fits(a, diff_op(a, b)), ap(a, diff_op(a, b)) == b,
{}

// transforming two ops that fit the same text yields ops that fit the other's result (ASSUMED:
// the OT crate's transform on equal base lengths; the padding is `fix_m`/`fix_t`)
#[verifier::external_body]
pub proof fn axiom_transform_fits(d: Seq<char>, m: int, t: int)
    requires fits(d, m), fits(d, t),
    ensures
        fits(ap(d, t), tr_my(fix_m(m, t), fix_t(m, t))),
        fits(ap(d, m), tr_their(fix_m(m, t), fix_t(m, t))),
{}

// a chain of ops each fitting the text produced by the previous ones
pub open spec fn vseq(d: Seq<char>, q: Seq<int>) -> bool
    decreases q.len(),
{
    if q.len() == 0 { true } else { fits(d, q[0]) && vseq(ap(d, q[0]), q.drop_first()) }
}

pub proof fn lemma_vseq_snoc(d: Seq<char>, q: Seq<int>, x: int)
    requires vseq(d, q), fits(fold(d, q), x),
    ensures vseq(d, q.push(x)),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(q.push(x).drop_first() =~= Seq::<int>::empty());
        assert(q.push(x)[0] == x);
        assert(fold(d, q) == d);
        assert(vseq(ap(d, x), Seq::<int>::empty()));
    } else {
        assert(q.push(x).drop_first() =~= q.drop_first().push(x));
        assert(q.push(x)[0] == q[0]);
        lemma_vseq_snoc(ap(d, q[0]), q.drop_first(), x);
    }
}

pub proof fn lemma_vseq_split(d: Seq<char>, q: Seq<int>, k: int)
    requires vseq(d, q), 0 <= k <= q.len(),
    ensures
        vseq(d, q.subrange(0, k)),
        vseq(fold(d, q.subrange(0, k)), q.subrange(k, q.len() as int)),
    decreases k,
{
    if k == 0 {
        assert(q.subrange(0, 0) =~= Seq::<int>::empty());
        assert(q.subrange(0, q.len() as int) =~= q);
    } else {
        // q[0..k] = q[0] ++ (q.drop_first())[0..k-1]
        lemma_vseq_split(ap(d, q[0]), q.drop_first(), k - 1);
        assert(q.subrange(0, k).drop_first() =~= q.drop_first().subrange(0, k - 1));
        assert(q.subrange(0, k)[0] == q[0]);
        assert(q.subrange(k, q.len() as int) =~= q.drop_first().subrange(k - 1, q.drop_first().len() as int));
        assert(fold(d, q.subrange(0, k)) == fold(ap(d, q[0]), q.drop_first().subrange(0, k - 1)));
    }
}

pub proof fn lemma_vseq_nth(d: Seq<char>, q: Seq<int>, k: int)
    requires vseq(d, q), 0 <= k < q.len(),
    ensures fits(fold(d, q.subrange(0, k)), q[k]),
{
    lemma_vseq_split(d, q, k);
    let r = q.subrange(k, q.len() as int);
    assert(r[0] == q[k]);
}

// transforming a fitting op through a fitting chain keeps everything fitting
pub proof fn lemma_vtt(d: Seq<char>, o: int, q: Seq<int>)
    requires vseq(d, q), fits(d, o),
    ensures
        fits(fold(d, q), tt(o, q).0),
        vseq(ap(d, o), tt(o, q).1),
    decreases q.len(),
{
    if q.len() > 0 {
        let m = q[0];
        let fm = fix_m(m, o);
        let ft = fix_t(m, o);
        axiom_transform_fits(d, m, o);
        axiom_tp1(d, fm, ft);
        lemma_fix(d, m, o);
        let o2 = tr_their(fm, ft);
        lemma_vtt(ap(d, m), o2, q.drop_first());
        let rest = tt(o2, q.drop_first()).1;
        // chain: tr_my(fm,ft) fits ap(d,o); then `rest` from ap(ap(d,o), tr_my) == ap(ap(d,m), o2)
        assert(ap(ap(d, o), tr_my(fm, ft)) == ap(ap(d, m), o2));
        let res = seq![tr_my(fm, ft)].add(rest);
        assert(res[0] == tr_my(fm, ft));
        assert(res.drop_first() =~= rest);
    }
}

// ---------- validity invariant of one session (on top of `inv`) ----------
pub open spec fn base(w: W) -> Seq<char> {
    fold(w.srv.lc, w.srv.q.subrange(0, w.ed.rd - confirmed(w.srv)))
}

pub open spec fn vinv(w: W) -> bool {
    &&& vseq(w.srv.lc, w.srv.q)
    &&& vseq(base(w), up_ops(w.up))
}

// editor rejects the daemon message at the head of `down` (VS Code: applyEdit failed): it is
// consumed, `rd` is not bumped, an empty edit with revision rd is sent and `re` is bumped.
pub open spec fn ed_reject(w: W) -> W {
    W { srv: w.srv, ed: Ed { buf: w.ed.buf, rd: w.ed.rd, re: w.ed.re + 1 },
        up: w.up.push(Up { rev: w.ed.rd, op: idop() }), down: w.down.drop_first() }
}

// the editor may reject only a message it would otherwise accept (rev == re); stale ones are ignored
pub open spec fn can_reject(w: W) -> bool { w.down.len() > 0 && w.down[0].rev == w.ed.re }

pub proof fn lemma_init_v(content: Seq<char>)
    ensures vinv(W {
        srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
        ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() }),
{
    let s = Srv { er: 0, dr: 0, q: Seq::<int>::empty(), lc: content, cur: content };
    assert(s.q.subrange(0, 0) =~= Seq::<int>::empty());
    assert(up_ops(Seq::<Up>::empty()) =~= Seq::<int>::empty());
}

pub proof fn lemma_reject(w: W)
    requires inv(w), vinv(w), can_reject(w),
    ensures inv(ed_reject(w)), vinv(ed_reject(w)),
{
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let w2 = ed_reject(w);
    let m = w.down[0];
    assert(m.rev <= s.er);
    // as for acceptance: m.rev == re >= er and m.rev <= er, so no edit in flight
    assert(s.er == e.re);
    assert(w.up.len() == 0);
    assert(up_ops(w.up) =~= Seq::<int>::empty());
    assert(up_ops(w2.up) =~= up_ops(w.up).push(idop()));
    let b = fold(s.lc, s.q.subrange(0, e.rd - c));
    assert(e.buf == b);
    axiom_id(e.buf);
    lemma_fold_snoc(b, up_ops(w.up), idop());
    assert(w2.up.len() == 1);
    assert(w2.up[0] == (Up { rev: e.rd, op: idop() }));
    assert forall|i: int| 0 <= i < w2.down.len() implies (#[trigger] w2.down[i]).rev <= s.er by {
        assert(w2.down[i] == w.down[i + 1]);
    }
    assert forall|i: int| 0 <= i < w2.down.len() && (#[trigger] w2.down[i]).rev == s.er
        implies c <= w2.down[i].g < s.dr && w2.down[i].op == s.q[w2.down[i].g - c] by {
        assert(w2.down[i] == w.down[i + 1]);
    }
    // vinv: base unchanged; [idop] fits base (= buf)
    assert(base(w2) == b);
    assert(up_ops(w2.up) =~= seq![idop()]);
    assert(seq![idop()].drop_first() =~= Seq::<int>::empty());
    assert(vseq(ap(b, idop()), Seq::<int>::empty()));
    assert(vseq(b, seq![idop()]));
}

// The rejection rule itself (VS Code applyEdit failure, nvim/emacs unappliable edit): the message is
// consumed, `rd` is unchanged, `re` is bumped, and an EMPTY edit with revision rd is sent.
pub proof fn lemma_reject_rule(w: W)
    requires can_reject(w),
    ensures
        ed_reject(w).ed.re == w.ed.re + 1,
        ed_reject(w).ed.rd == w.ed.rd,
        ed_reject(w).up == w.up.push(Up { rev: w.ed.rd, op: idop() }),
        ed_reject(w).down == w.down.drop_first(),
{}

pub proof fn lemma_crdt_step_v(w: W, o: int)
    requires inv(w), vinv(w), fits(w.srv.cur, o),
    ensures vinv(crdt_step(w, o)),
{
    let s = w.srv; let c = confirmed(s);
    lemma_fold_snoc(s.lc, s.q, o);
    lemma_vseq_snoc(s.lc, s.q, o);
    assert(s.q.push(o).subrange(0, w.ed.rd - c) =~= s.q.subrange(0, w.ed.rd - c));
}

pub proof fn lemma_ed_local_v(w: W, o: int)
    requires inv(w), vinv(w), fits(w.ed.buf, o),
    ensures vinv(ed_local(w, o)),
{
    let w2 = ed_local(w, o);
    assert(up_ops(w2.up) =~= up_ops(w.up).push(o));
    lemma_vseq_snoc(base(w), up_ops(w.up), o);
}

// the daemon's `apply_editor_operation` succeeds for the head edit (rev in range, op fits), and
// the transformed op fits the daemon's current content
pub proof fn lemma_srv_recv_v(w: W)
    requires inv(w), vinv(w), w.up.len() > 0,
    ensures
        vinv(srv_recv(w)),
        fits(w.srv.cur, tt(w.up[0].op, w.srv.q.subrange(w.ed.rd - confirmed(w.srv), w.srv.q.len() as int)).0),
        fits(base(w), w.up[0].op),
{
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let u = w.up[0];
    let k = (e.rd - c) as int;
    let lc1 = fold(s.lc, s.q.subrange(0, k));
    let q1 = s.q.subrange(k, s.q.len() as int);
    assert(u.rev == e.rd);
    lemma_vseq_split(s.lc, s.q, k);
    let ops = up_ops(w.up);
    assert(ops[0] == u.op);
    assert(fits(lc1, u.op));
    lemma_vtt(lc1, u.op, q1);
    lemma_fold_split(s.lc, s.q, k);
    assert(s.cur == fold(lc1, q1));
    let w2 = srv_recv(w);
    let r = srv_edit(s, u.rev, u.op);
    assert(r.0.q == tt(u.op, q1).1);
    assert(r.0.lc == ap(lc1, u.op));
    assert(up_ops(w2.up) =~= ops.drop_first());
    assert(confirmed(r.0) == e.rd) by {
        lemma_srv_edit_wf(s, u.rev, u.op);
        lemma_tt(lc1, u.op, q1);
    }
    assert(r.0.q.subrange(0, 0) =~= Seq::<int>::empty());
    assert(base(w2) == ap(lc1, u.op));
}

pub proof fn lemma_ed_recv_v(w: W)
    requires inv(w), vinv(w), w.down.len() > 0,
    ensures
        vinv(ed_recv(w)),
        // an accepted message always fits the editor's buffer: a correct editor never has to reject
        w.down[0].rev == w.ed.re ==> fits(w.ed.buf, w.down[0].op),
{
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let m = w.down[0];
    let w2 = ed_recv(w);
    if m.rev == e.re {
        assert(s.er == e.re);
        assert(w.up.len() == 0);
        assert(m.g == e.rd && e.rd < s.dr);
        assert(m.op == s.q[e.rd - c]);
        let k = (e.rd - c) as int;
        lemma_vseq_nth(s.lc, s.q, k);
        assert(up_ops(w.up) =~= Seq::<int>::empty());
        assert(e.buf == base(w));
        assert(s.q.subrange(0, k + 1) =~= s.q.subrange(0, k).push(s.q[k]));
        lemma_fold_snoc(s.lc, s.q.subrange(0, k), s.q[k]);
        assert(up_ops(w2.up) =~= Seq::<int>::empty());
    } else {
        assert(base(w2) == base(w));
    }
}

// =====================================================================================
// EXTENSION 2: several editors on one document, connect/disconnect/reopen, and liveness.
//
// Real structure (editor_connection.rs, daemon.rs): one `EditorConnection` per editor, one
// `OTServer` per (editor, file), and the daemon's CRDT as the hub. An edit from editor i goes
// through server i, then the transformed op is applied to the CRDT and sent to every other
// editor's server (`process_component_message` -> `broadcast_to_editors` -> `message_from_inside`
// -> `apply_crdt_change`). A change from outside (peers, disk) goes to all servers. All this runs
// inside one actor step, so it is atomic. Editor i's session is `Some(w)` while it has the file
// open; `None` while it does not.
//
// ASSUMED here (daemon.rs layer, not verified): while any editor has the file open, the CRDT keeps
// the file's text (a deletion by a peer is not applied to open editors, see daemon.rs
// `FileRemoval`); and an editor's session starts fresh: messages from its previous session are
// discarded by the editor before the new session starts (see DESIGN.md, "reopen").
// =====================================================================================

pub struct G {
    pub crdt: Seq<char>,        // the daemon's CRDT text of the file
    pub ss: Seq<Option<W>>,     // per editor: session state, None = file not open in that editor
    pub inp: nat,               // ghost budget: remaining input steps (CRDT change, typing, open, close)
    pub rej: nat,               // ghost budget: remaining editor rejections (fair acceptance)
}

pub open spec fn sinv(w: W) -> bool { inv(w) && vinv(w) }

pub open spec fn sess_ok(o: Option<W>, crdt: Seq<char>) -> bool {
    match o { Some(w) => sinv(w) && w.srv.cur == crdt, None => true }
}

pub open spec fn ginv(g: G) -> bool {
    forall|i: int| 0 <= i < g.ss.len() ==> sess_ok(#[trigger] g.ss[i], g.crdt)
}

pub open spec fn fresh(b: Seq<char>) -> W {
    W { srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: b, cur: b },
        ed: Ed { buf: b, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() }
}

// deliver a CRDT-side op to every session except `skip`
pub open spec fn bcast(ss: Seq<Option<W>>, skip: int, o: int) -> Seq<Option<W>> {
    Seq::new(ss.len(), |j: int| match ss[j] {
        Some(w) => if j == skip { Some(w) } else { Some(crdt_step(w, o)) },
        None => None,
    })
}

pub open spec fn qtail(w: W) -> Seq<int> {
    w.srv.q.subrange(w.ed.rd - confirmed(w.srv), w.srv.q.len() as int)
}

// the op the CRDT receives when the daemon processes session w's head edit
pub open spec fn crdt_op_of(w: W) -> int { tt(w.up[0].op, qtail(w)).0 }

pub open spec fn some_w(g: G, i: int) -> bool { 0 <= i < g.ss.len() && g.ss[i] is Some }
pub open spec fn w_at(g: G, i: int) -> W { g.ss[i].unwrap() }

// --- input steps (consume `inp`) ---
// a change from outside (other peer, disk) to the CRDT
pub open spec fn g_crdt(g: G, o: int) -> G {
    G { crdt: ap(g.crdt, o), ss: bcast(g.ss, -1, o), inp: (g.inp - 1) as nat, rej: g.rej }
}
// editor i types
pub open spec fn g_local(g: G, i: int, o: int) -> G {
    G { crdt: g.crdt, ss: g.ss.update(i, Some(ed_local(w_at(g, i), o))), inp: (g.inp - 1) as nat, rej: g.rej }
}
// editor i opens the file with buffer content b (replaces a session of its own)
pub open spec fn g_open(g: G, i: int, b: Seq<char>) -> G {
    let w1 = if b == g.crdt { fresh(b) } else { crdt_step(fresh(b), diff_op(b, g.crdt)) };
    G { crdt: g.crdt, ss: g.ss.update(i, Some(w1)), inp: (g.inp - 1) as nat, rej: g.rej }
}
// editor i closes the file or disconnects: its in-flight messages are gone
pub open spec fn g_close(g: G, i: int) -> G {
    G { crdt: g.crdt, ss: g.ss.update(i, None), inp: (g.inp - 1) as nat, rej: g.rej }
}

// --- delivery steps ---
// the daemon processes the next edit of editor i
pub open spec fn g_srv(g: G, i: int) -> G {
    let w = w_at(g, i);
    let o = crdt_op_of(w);
    G { crdt: ap(g.crdt, o), ss: bcast(g.ss, i, o).update(i, Some(srv_recv(w))), inp: g.inp, rej: g.rej }
}
// editor i handles the next daemon message (applies or ignores it)
pub open spec fn g_ed(g: G, i: int) -> G {
    G { crdt: g.crdt, ss: g.ss.update(i, Some(ed_recv(w_at(g, i)))), inp: g.inp, rej: g.rej }
}
// editor i rejects the next daemon message
pub open spec fn g_rej(g: G, i: int) -> G {
    G { crdt: g.crdt, ss: g.ss.update(i, Some(ed_reject(w_at(g, i)))), inp: g.inp, rej: (g.rej - 1) as nat }
}

// ---------- sums for the liveness measure ----------
pub open spec fn ul(o: Option<W>) -> nat { match o { Some(w) => w.up.len(), None => 0 } }
pub open spec fn dl(o: Option<W>) -> nat { match o { Some(w) => w.down.len(), None => 0 } }

pub open spec fn sum_u(ss: Seq<Option<W>>, n: nat) -> nat decreases n {
    if n == 0 { 0 } else { sum_u(ss, (n - 1) as nat) + ul(ss[n - 1]) }
}
pub open spec fn sum_d(ss: Seq<Option<W>>, n: nat) -> nat decreases n {
    if n == 0 { 0 } else { sum_d(ss, (n - 1) as nat) + dl(ss[n - 1]) }
}

pub proof fn lemma_sum_u_update(ss: Seq<Option<W>>, i: int, v: Option<W>, n: nat)
    requires 0 <= i < n <= ss.len(),
    ensures sum_u(ss.update(i, v), n) + ul(ss[i]) == sum_u(ss, n) + ul(v),
    decreases n,
{
    if i < n - 1 { lemma_sum_u_update(ss, i, v, (n - 1) as nat); }
    else { lemma_sum_u_same_prefix(ss, ss.update(i, v), (n - 1) as nat); }
}
pub proof fn lemma_sum_u_same_prefix(a: Seq<Option<W>>, b: Seq<Option<W>>, n: nat)
    requires n <= a.len(), n <= b.len(), forall|j: int| 0 <= j < n ==> a[j] == b[j],
    ensures sum_u(a, n) == sum_u(b, n),
    decreases n,
{ if n > 0 { lemma_sum_u_same_prefix(a, b, (n - 1) as nat); } }

pub proof fn lemma_sum_d_update(ss: Seq<Option<W>>, i: int, v: Option<W>, n: nat)
    requires 0 <= i < n <= ss.len(),
    ensures sum_d(ss.update(i, v), n) + dl(ss[i]) == sum_d(ss, n) + dl(v),
    decreases n,
{
    if i < n - 1 { lemma_sum_d_update(ss, i, v, (n - 1) as nat); }
    else { lemma_sum_d_same_prefix(ss, ss.update(i, v), (n - 1) as nat); }
}
pub proof fn lemma_sum_d_same_prefix(a: Seq<Option<W>>, b: Seq<Option<W>>, n: nat)
    requires n <= a.len(), n <= b.len(), forall|j: int| 0 <= j < n ==> a[j] == b[j],
    ensures sum_d(a, n) == sum_d(b, n),
    decreases n,
{ if n > 0 { lemma_sum_d_same_prefix(a, b, (n - 1) as nat); } }

// broadcasting does not change any session's `up`
pub proof fn lemma_sum_u_bcast(ss: Seq<Option<W>>, skip: int, o: int, n: nat)
    requires n <= ss.len(),
    ensures sum_u(bcast(ss, skip, o), n) == sum_u(ss, n),
    decreases n,
{
    if n > 0 {
        lemma_sum_u_bcast(ss, skip, o, (n - 1) as nat);
        assert(ul(bcast(ss, skip, o)[n - 1]) == ul(ss[n - 1]));
    }
}

pub open spec fn lex_lt(a: (nat, nat, nat, nat), b: (nat, nat, nat, nat)) -> bool {
    a.0 < b.0 || (a.0 == b.0 && (a.1 < b.1 || (a.1 == b.1 && (a.2 < b.2 || (a.2 == b.2 && a.3 < b.3)))))
}
pub open spec fn mu(g: G) -> (nat, nat, nat, nat) {
    (g.inp, g.rej, sum_u(g.ss, g.ss.len()), sum_d(g.ss, g.ss.len()))
}

// ---------- every step keeps `ginv` and strictly decreases mu ----------
pub proof fn lemma_g_crdt(g: G, o: int)
    requires ginv(g), g.inp > 0, fits(g.crdt, o),
    ensures ginv(g_crdt(g, o)), lex_lt(mu(g_crdt(g, o)), mu(g)),
{
    let g2 = g_crdt(g, o);
    assert forall|i: int| 0 <= i < g2.ss.len() implies sess_ok(#[trigger] g2.ss[i], g2.crdt) by {
        if let Some(w) = g.ss[i] {
            lemma_crdt_step(w, o);
            lemma_crdt_step_v(w, o);
        }
    }
}

pub proof fn lemma_g_local(g: G, i: int, o: int)
    requires ginv(g), g.inp > 0, some_w(g, i), fits(w_at(g, i).ed.buf, o),
    ensures ginv(g_local(g, i, o)), lex_lt(mu(g_local(g, i, o)), mu(g)),
{
    let g2 = g_local(g, i, o);
    let w = w_at(g, i);
    lemma_ed_local(w, o);
    lemma_ed_local_v(w, o);
    assert forall|j: int| 0 <= j < g2.ss.len() implies sess_ok(#[trigger] g2.ss[j], g2.crdt) by {
        if j != i { assert(g2.ss[j] == g.ss[j]); }
    }
}

pub proof fn lemma_g_open(g: G, i: int, b: Seq<char>)
    requires ginv(g), g.inp > 0, 0 <= i < g.ss.len(),
    ensures ginv(g_open(g, i, b)), lex_lt(mu(g_open(g, i, b)), mu(g)),
{
    let g2 = g_open(g, i, b);
    lemma_init(b);
    lemma_init_v(b);
    if b != g.crdt {
        axiom_diff(b, g.crdt);
        lemma_crdt_step(fresh(b), diff_op(b, g.crdt));
        lemma_crdt_step_v(fresh(b), diff_op(b, g.crdt));
    }
    assert forall|j: int| 0 <= j < g2.ss.len() implies sess_ok(#[trigger] g2.ss[j], g2.crdt) by {
        if j != i { assert(g2.ss[j] == g.ss[j]); }
    }
}

pub proof fn lemma_g_close(g: G, i: int)
    requires ginv(g), g.inp > 0, 0 <= i < g.ss.len(),
    ensures ginv(g_close(g, i)), lex_lt(mu(g_close(g, i)), mu(g)),
{
    let g2 = g_close(g, i);
    assert forall|j: int| 0 <= j < g2.ss.len() implies sess_ok(#[trigger] g2.ss[j], g2.crdt) by {
        if j != i { assert(g2.ss[j] == g.ss[j]); }
    }
}

pub proof fn lemma_g_srv(g: G, i: int)
    requires ginv(g), some_w(g, i), w_at(g, i).up.len() > 0,
    ensures ginv(g_srv(g, i)), lex_lt(mu(g_srv(g, i)), mu(g)),
{
    let g2 = g_srv(g, i);
    let w = w_at(g, i);
    let o = crdt_op_of(w);
    lemma_srv_recv(w);
    lemma_srv_recv_v(w);
    // the daemon's content equals the CRDT's, so the transformed op fits the CRDT
    assert(w.srv.cur == g.crdt);
    let b = bcast(g.ss, i, o);
    assert forall|j: int| 0 <= j < g2.ss.len() implies sess_ok(#[trigger] g2.ss[j], g2.crdt) by {
        if j == i {
            assert(g2.ss[j] == Some(srv_recv(w)));
            assert(srv_recv(w).srv.cur == ap(w.srv.cur, o));
        } else {
            assert(g2.ss[j] == b[j]);
            if let Some(wj) = g.ss[j] {
                lemma_crdt_step(wj, o);
                lemma_crdt_step_v(wj, o);
            }
        }
    }
    let n = g.ss.len();
    lemma_sum_u_bcast(g.ss, i, o, n);
    lemma_sum_u_update(b, i, Some(srv_recv(w)), n);
    assert(b[i] == g.ss[i]);
}

pub proof fn lemma_g_ed(g: G, i: int)
    requires ginv(g), some_w(g, i), w_at(g, i).down.len() > 0,
    ensures ginv(g_ed(g, i)), lex_lt(mu(g_ed(g, i)), mu(g)),
{
    let g2 = g_ed(g, i);
    let w = w_at(g, i);
    lemma_ed_recv(w);
    lemma_ed_recv_v(w);
    assert forall|j: int| 0 <= j < g2.ss.len() implies sess_ok(#[trigger] g2.ss[j], g2.crdt) by {
        if j != i { assert(g2.ss[j] == g.ss[j]); }
    }
    let n = g.ss.len();
    lemma_sum_u_update(g.ss, i, Some(ed_recv(w)), n);
    lemma_sum_d_update(g.ss, i, Some(ed_recv(w)), n);
}

pub proof fn lemma_g_rej(g: G, i: int)
    requires ginv(g), g.rej > 0, some_w(g, i), can_reject(w_at(g, i)),
    ensures ginv(g_rej(g, i)), lex_lt(mu(g_rej(g, i)), mu(g)),
{
    let g2 = g_rej(g, i);
    let w = w_at(g, i);
    lemma_reject(w);
    assert forall|j: int| 0 <= j < g2.ss.len() implies sess_ok(#[trigger] g2.ss[j], g2.crdt) by {
        if j != i { assert(g2.ss[j] == g.ss[j]); }
    }
}

// the initial world: no editor has the file open
pub proof fn lemma_g_init(crdt: Seq<char>, n: nat, inp: nat, rej: nat)
    ensures ginv(G { crdt, ss: Seq::new(n, |j: int| None), inp, rej }),
{}

// ---------- agreement and liveness ----------
pub open spec fn quiescent(g: G) -> bool {
    forall|i: int| 0 <= i < g.ss.len() ==> match #[trigger] g.ss[i] {
        Some(w) => w.up.len() == 0 && w.down.len() == 0,
        None => true,
    }
}

// when nothing is in flight, every editor that has the file open matches the daemon's CRDT
pub proof fn theorem_agreement(g: G)
    requires ginv(g), quiescent(g),
    ensures forall|i: int| 0 <= i < g.ss.len() ==> match #[trigger] g.ss[i] {
        Some(w) => w.ed.buf == g.crdt && w.ed.rd == w.srv.dr,
        None => true,
    },
{
    assert forall|i: int| 0 <= i < g.ss.len() implies match #[trigger] g.ss[i] {
        Some(w) => w.ed.buf == g.crdt && w.ed.rd == w.srv.dr,
        None => true,
    } by {
        if let Some(w) = g.ss[i] { theorem_quiescent_agreement(w); }
    }
}

// delivery steps: 0 = daemon takes editor i's next edit, 1 = editor i handles its next daemon
// message, 2 = editor i rejects it (uses the rejection budget)
pub open spec fn enabled(g: G, k: int, i: int) -> bool {
    some_w(g, i) && (
        (k == 0 && w_at(g, i).up.len() > 0)
        || (k == 1 && w_at(g, i).down.len() > 0)
        || (k == 2 && g.rej > 0 && can_reject(w_at(g, i))))
}
pub open spec fn deliver(g: G, k: int, i: int) -> G {
    if k == 0 { g_srv(g, i) } else if k == 1 { g_ed(g, i) } else { g_rej(g, i) }
}

// progress: if something is in flight, a delivery step is enabled
pub proof fn lemma_progress(g: G)
    requires !quiescent(g),
    ensures exists|i: int| enabled(g, 0, i) || enabled(g, 1, i),
{
    let i = choose|i: int| 0 <= i < g.ss.len() && !(match #[trigger] g.ss[i] {
        Some(w) => w.up.len() == 0 && w.down.len() == 0, None => true });
    let w = g.ss[i].unwrap();
    if w.up.len() > 0 { assert(enabled(g, 0, i)); } else { assert(enabled(g, 1, i)); }
}

// every delivery step preserves ginv and decreases mu
pub proof fn lemma_deliver(g: G, k: int, i: int)
    requires ginv(g), enabled(g, k, i),
    ensures ginv(deliver(g, k, i)), lex_lt(mu(deliver(g, k, i)), mu(g)),
{
    if k == 0 { lemma_g_srv(g, i); } else if k == 1 { lemma_g_ed(g, i); } else { lemma_g_rej(g, i); }
}

// ANY scheduler that always picks an enabled delivery step (so it never idles while a message is
// in flight: this is fair delivery) reaches quiescence from any state: every execution is finite
// because `mu` strictly decreases, and the end state has every open editor matching the daemon.
// `sched(n, g)` is the scheduler's pick (kind, editor) at its n-th step; the budgets `inp`/`rej`
// are not touched by deliveries except `rej` by rejections, which is what bounds them.
pub open spec fn run(g: G, sched: spec_fn(nat, G) -> (int, int), n0: nat, n: nat) -> G
    decreases n,
{
    if n == 0 || quiescent(g) { g } else {
        let c = sched(n0, g);
        run(deliver(g, c.0, c.1), sched, n0 + 1, (n - 1) as nat)
    }
}

pub open spec fn fair(sched: spec_fn(nat, G) -> (int, int)) -> bool {
    forall|m: nat, r: G| ginv(r) && !quiescent(r) ==> enabled(r, #[trigger] sched(m, r).0, sched(m, r).1)
}

pub proof fn lemma_run_inv(g: G, sched: spec_fn(nat, G) -> (int, int), n0: nat, n: nat)
    requires ginv(g), fair(sched),
    ensures ginv(run(g, sched, n0, n)),
    decreases n,
{
    if n > 0 && !quiescent(g) {
        let c = sched(n0, g);
        lemma_deliver(g, c.0, c.1);
        lemma_run_inv(deliver(g, c.0, c.1), sched, n0 + 1, (n - 1) as nat);
    }
}

pub proof fn lemma_terminates(g: G, sched: spec_fn(nat, G) -> (int, int), n0: nat)
    requires ginv(g), fair(sched),
    ensures exists|n: nat| quiescent(#[trigger] run(g, sched, n0, n)),
    decreases mu(g).0, mu(g).1, mu(g).2, mu(g).3,
{
    if quiescent(g) {
        assert(run(g, sched, n0, 0) == g);
    } else {
        let c = sched(n0, g);
        lemma_deliver(g, c.0, c.1);
        let g2 = deliver(g, c.0, c.1);
        lemma_terminates(g2, sched, n0 + 1);
        let n = choose|n: nat| quiescent(#[trigger] run(g2, sched, n0 + 1, n));
        assert(run(g, sched, n0, n + 1) == run(g2, sched, n0 + 1, n));
    }
}

// the liveness theorem: eventually (after inputs stop) all open editors match the daemon
pub open spec fn all_match(r: G) -> bool {
    ginv(r) && quiescent(r)
    && forall|i: int| 0 <= i < r.ss.len() ==> match #[trigger] r.ss[i] {
        Some(w) => w.ed.buf == r.crdt,
        None => true,
    }
}

pub proof fn theorem_liveness(g: G, sched: spec_fn(nat, G) -> (int, int))
    requires ginv(g), fair(sched),
    ensures exists|n: nat| all_match(#[trigger] run(g, sched, 0, n)),
{
    lemma_terminates(g, sched, 0);
    let n = choose|n: nat| quiescent(#[trigger] run(g, sched, 0, n));
    lemma_run_inv(g, sched, 0, n);
    theorem_agreement(run(g, sched, 0, n));
}

// non-vacuity: a fair scheduler exists (some enabled step exists in every non-quiescent state
// whose rejections are not needed), so `theorem_liveness` is not about an empty class.
pub proof fn lemma_fair_exists()
    ensures exists|sched: spec_fn(nat, G) -> (int, int)| fair(sched),
{
    let sched = |m: nat, r: G| -> (int, int) {
        if quiescent(r) { (0, 0) } else {
            let i = choose|i: int| enabled(r, 0, i) || enabled(r, 1, i);
            if enabled(r, 0, i) { (0, i) } else { (1, i) }
        }
    };
    assert forall|m: nat, r: G| ginv(r) && !quiescent(r) implies enabled(r, #[trigger] sched(m, r).0, sched(m, r).1) by {
        lemma_progress(r);
        let i = choose|i: int| enabled(r, 0, i) || enabled(r, 1, i);
        assert(enabled(r, 0, i) || enabled(r, 1, i));
    }
    assert(fair(sched));
}

// =====================================================================================
// Part 4: interleaved inputs, and the first open of a file the CRDT does not have yet.
// =====================================================================================

// A step of the full system: a delivery (kind 0..2, editor i) or an input (kind 3: CRDT change o,
// 4: editor i types o, 5: editor i opens with buffer b, 6: editor i closes).
pub struct Cmd { pub k: int, pub i: int, pub o: int, pub b: Seq<char> }

pub open spec fn enabled_full(g: G, c: Cmd) -> bool {
    if c.k <= 2 { enabled(g, c.k, c.i) }
    else if c.k == 3 { g.inp > 0 && fits(g.crdt, c.o) }
    else if c.k == 4 { g.inp > 0 && some_w(g, c.i) && fits(w_at(g, c.i).ed.buf, c.o) }
    else if c.k == 5 { g.inp > 0 && 0 <= c.i < g.ss.len() }
    else if c.k == 6 { g.inp > 0 && 0 <= c.i < g.ss.len() }
    else { false }
}
pub open spec fn step_full(g: G, c: Cmd) -> G {
    if c.k <= 2 { deliver(g, c.k, c.i) }
    else if c.k == 3 { g_crdt(g, c.o) }
    else if c.k == 4 { g_local(g, c.i, c.o) }
    else if c.k == 5 { g_open(g, c.i, c.b) }
    else { g_close(g, c.i) }
}

pub proof fn lemma_step_full(g: G, c: Cmd)
    requires ginv(g), enabled_full(g, c),
    ensures ginv(step_full(g, c)), lex_lt(mu(step_full(g, c)), mu(g)),
{
    if c.k <= 2 { lemma_deliver(g, c.k, c.i); }
    else if c.k == 3 { lemma_g_crdt(g, c.o); }
    else if c.k == 4 { lemma_g_local(g, c.i, c.o); }
    else if c.k == 5 { lemma_g_open(g, c.i, c.b); }
    else { lemma_g_close(g, c.i); }
}

pub open spec fn run_full(g: G, sched: spec_fn(nat, G) -> Cmd, n0: nat, n: nat) -> G
    decreases n,
{
    if n == 0 || quiescent(g) { g } else {
        run_full(step_full(g, sched(n0, g)), sched, n0 + 1, (n - 1) as nat)
    }
}

// the scheduler may interleave ANY enabled step, inputs included, until the system is quiet
pub open spec fn fair_full(sched: spec_fn(nat, G) -> Cmd) -> bool {
    forall|m: nat, r: G| ginv(r) && !quiescent(r) ==> enabled_full(r, #[trigger] sched(m, r))
}

pub proof fn lemma_terminates_full(g: G, sched: spec_fn(nat, G) -> Cmd, n0: nat)
    requires ginv(g), fair_full(sched),
    ensures exists|n: nat| quiescent(#[trigger] run_full(g, sched, n0, n)) && ginv(run_full(g, sched, n0, n)),
    decreases mu(g).0, mu(g).1, mu(g).2, mu(g).3,
{
    if quiescent(g) {
        assert(run_full(g, sched, n0, 0) == g);
    } else {
        let c = sched(n0, g);
        lemma_step_full(g, c);
        let g2 = step_full(g, c);
        lemma_terminates_full(g2, sched, n0 + 1);
        let n = choose|n: nat| quiescent(#[trigger] run_full(g2, sched, n0 + 1, n)) && ginv(run_full(g2, sched, n0 + 1, n));
        assert(run_full(g, sched, n0, n + 1) == run_full(g2, sched, n0 + 1, n));
    }
}

// every interleaving of inputs and deliveries is finite and ends with all open editors equal to the daemon
pub proof fn theorem_liveness_interleaved(g: G, sched: spec_fn(nat, G) -> Cmd)
    requires ginv(g), fair_full(sched),
    ensures exists|n: nat| all_match(#[trigger] run_full(g, sched, 0, n)),
{
    lemma_terminates_full(g, sched, 0);
    let n = choose|n: nat| quiescent(#[trigger] run_full(g, sched, 0, n)) && ginv(run_full(g, sched, 0, n));
    theorem_agreement(run_full(g, sched, 0, n));
}

// non-vacuity: a fair_full scheduler exists (it may pick inputs while the budget lasts)
pub proof fn lemma_fair_full_exists()
    ensures exists|sched: spec_fn(nat, G) -> Cmd| fair_full(sched),
{
    let sched = |m: nat, r: G| -> Cmd {
        if quiescent(r) { Cmd { k: 0, i: 0, o: 0, b: Seq::empty() } } else {
            let i = choose|i: int| enabled(r, 0, i) || enabled(r, 1, i);
            if enabled(r, 0, i) { Cmd { k: 0, i, o: 0, b: Seq::empty() } } else { Cmd { k: 1, i, o: 0, b: Seq::empty() } }
        }
    };
    assert forall|m: nat, r: G| ginv(r) && !quiescent(r) implies enabled_full(r, #[trigger] sched(m, r)) by {
        lemma_progress(r);
        let i = choose|i: int| enabled(r, 0, i) || enabled(r, 1, i);
        assert(enabled(r, 0, i) || enabled(r, 1, i));
    }
    assert(fair_full(sched));
}

// A scheduler that does use an input: closing an open editor is enabled whenever inp > 0.
pub proof fn lemma_input_step_exists(g: G, i: int)
    requires ginv(g), g.inp > 0, 0 <= i < g.ss.len(),
    ensures enabled_full(g, Cmd { k: 6, i, o: 0, b: Seq::empty() }),
{}

// First open of a file the CRDT does not have yet (`Open` else-branch: `set_file(content)`):
// no editor has it open (an open editor keeps the file in the CRDT), the CRDT becomes the buffer,
// and no diff is sent.
pub open spec fn g_open_new(g: G, i: int, b: Seq<char>) -> G {
    G { crdt: b, ss: g.ss.update(i, Some(fresh(b))), inp: (g.inp - 1) as nat, rej: g.rej }
}
pub proof fn lemma_g_open_new(g: G, i: int, b: Seq<char>)
    requires ginv(g), g.inp > 0, 0 <= i < g.ss.len(),
        forall|j: int| 0 <= j < g.ss.len() && j != i ==> g.ss[j] is None,
    ensures ginv(g_open_new(g, i, b)), lex_lt(mu(g_open_new(g, i, b)), mu(g)),
{
    let g2 = g_open_new(g, i, b);
    lemma_init(b);
    lemma_init_v(b);
    assert forall|j: int| 0 <= j < g2.ss.len() implies sess_ok(#[trigger] g2.ss[j], g2.crdt) by {
        if j != i { assert(g2.ss[j] == g.ss[j]); }
    }
}

// The broadcast rule itself: when the daemon processes editor i's edit, every OTHER open editor
// receives the transformed op (`broadcast_to_editors` excludes only the sender).
pub proof fn lemma_g_srv_broadcast(g: G, i: int)
    requires some_w(g, i), w_at(g, i).up.len() > 0,
    ensures forall|j: int| 0 <= j < g.ss.len() && j != i && g.ss[j] is Some ==>
        g_srv(g, i).ss[j] == Some(crdt_step(g.ss[j].unwrap(), crdt_op_of(w_at(g, i)))),
{}

} // verus!
fn main() {}
