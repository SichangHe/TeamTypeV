// (authored by agents) NEGATIVE CONTROL: panic_crdt_op_not_required_to_fit; Verus must reject it.
// (authored by agents) Verus proof that no length-related failure (a panic in the daemon) occurs when
// the daemon feeds operations to the CRDT and to the editors' OT servers: every operation fits the
// text it is applied to. Length-tracking extension of the one-editor protocol of conc.rs.
use vstd::prelude::*;
#[path = "../../concurrency/teamtype_concurrency.rs"]
mod conc;
use conc::*;

verus! {

// ---------- trusted length facts of the operational-transform crate (ASSUMED) ----------
// They restate postconditions the round2/tp1 proof verifies for its source-derived copy of
// operational-transform 0.6.1 (`transform`: a'.base_len == other.target_len, b'.base_len ==
// self.target_len, a'.target_len == b'.target_len; `retain(n)`: base and target length grow by n;
// `apply` of an op with base_len <= len keeps the unread tail). They are NOT proved here.
pub uninterp spec fn tgt_len_of(o: int) -> nat;

#[verifier::external_body]
pub proof fn axiom_ap_len(d: Seq<char>, o: int)
    requires base_len_of(o) <= d.len(),
    ensures ap(d, o).len() == d.len() - base_len_of(o) + tgt_len_of(o),
{}
#[verifier::external_body]
pub proof fn axiom_pad_len(o: int, n: nat)
    ensures base_len_of(pad(o, n)) == base_len_of(o) + n, tgt_len_of(pad(o, n)) == tgt_len_of(o) + n,
{}
#[verifier::external_body]
pub proof fn axiom_tr_len(m: int, t: int)
    requires base_len_of(m) == base_len_of(t),
    ensures
        base_len_of(tr_my(m, t)) == tgt_len_of(t),
        base_len_of(tr_their(m, t)) == tgt_len_of(m),
        tgt_len_of(tr_my(m, t)) == tgt_len_of(tr_their(m, t)),
{}

// an op fits a text when its base length is within the text (apply/force_apply then cannot fail)
pub open spec fn fits(d: Seq<char>, o: int) -> bool { base_len_of(o) <= d.len() }

// the chain of ops q applied one after the other, each fitting the text it meets
pub open spec fn chain_fits(d: Seq<char>, q: Seq<int>) -> bool
    decreases q.len(),
{
    if q.len() == 0 { true } else { fits(d, q[0]) && chain_fits(ap(d, q[0]), q.drop_first()) }
}

pub proof fn lemma_chain_push(d: Seq<char>, q: Seq<int>, x: int)
    ensures chain_fits(d, q.push(x)) == (chain_fits(d, q) && fits(fold(d, q), x)),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(q.push(x).drop_first() =~= Seq::<int>::empty());
        assert(q.push(x)[0] == x);
        assert(chain_fits(ap(d, x), Seq::<int>::empty()));
        assert(fold(d, q) == d);
    } else {
        assert(q.push(x).drop_first() =~= q.drop_first().push(x));
        assert(q.push(x)[0] == q[0]);
        lemma_chain_push(ap(d, q[0]), q.drop_first(), x);
        assert(fold(d, q) == fold(ap(d, q[0]), q.drop_first()));
    }
}

// splitting a chain
pub proof fn lemma_chain_split(d: Seq<char>, q: Seq<int>, k: int)
    requires 0 <= k <= q.len(),
    ensures
        chain_fits(d, q) == (chain_fits(d, q.subrange(0, k))
            && chain_fits(fold(d, q.subrange(0, k)), q.subrange(k, q.len() as int))),
    decreases k,
{
    if k == 0 {
        assert(q.subrange(0, 0) =~= Seq::<int>::empty());
        assert(q.subrange(0, q.len() as int) =~= q);
    } else {
        assert(q.subrange(0, k) =~= q.subrange(0, k - 1).push(q[k - 1]));
        lemma_chain_push(d, q.subrange(0, k - 1), q[k - 1]);
        lemma_chain_split(d, q, k - 1);
        lemma_fold_snoc(d, q.subrange(0, k - 1), q[k - 1]);
        let r = q.subrange(k - 1, q.len() as int);
        assert(r.drop_first() =~= q.subrange(k, q.len() as int));
        assert(r[0] == q[k - 1]);
        // chain_fits(x, r) == fits(x, r0) && chain_fits(ap(x, r0), r.drop_first())
        let x = fold(d, q.subrange(0, k - 1));
        assert(chain_fits(x, r) == (fits(x, q[k - 1]) && chain_fits(ap(x, q[k - 1]), q.subrange(k, q.len() as int))));
    }
}

// padding keeps both ops fitting and makes their base lengths equal (the daemon's `fix_m`/`fix_t`)
pub proof fn lemma_fix_fits(d: Seq<char>, m: int, o: int)
    requires fits(d, m), fits(d, o),
    ensures
        base_len_of(fix_m(m, o)) == base_len_of(fix_t(m, o)),
        fits(d, fix_m(m, o)), fits(d, fix_t(m, o)),
        ap(d, fix_m(m, o)) == ap(d, m), ap(d, fix_t(m, o)) == ap(d, o),
        ap(d, fix_m(m, o)).len() == ap(d, m).len(),
        ap(d, fix_t(m, o)).len() == ap(d, o).len(),
{
    lemma_fix(d, m, o);
    if base_len_of(m) < base_len_of(o) {
        axiom_pad_len(m, (base_len_of(o) - base_len_of(m)) as nat);
    } else {
        axiom_pad_len(o, (base_len_of(m) - base_len_of(o)) as nat);
    }
}

// transform_through_operations keeps every op fitting, including the transformed incoming one
pub proof fn lemma_tt_fit(d: Seq<char>, o: int, q: Seq<int>)
    requires fits(d, o), chain_fits(d, q),
    ensures
        chain_fits(ap(d, o), tt(o, q).1),
        fits(fold(d, q), tt(o, q).0),
    decreases q.len(),
{
    if q.len() == 0 {
    } else {
        let m = q[0];
        let fm = fix_m(m, o);
        let ft = fix_t(m, o);
        lemma_fix_fits(d, m, o);
        axiom_tp1(d, fm, ft);
        axiom_tr_len(fm, ft);
        axiom_ap_len(d, fm);
        axiom_ap_len(d, ft);
        let o2 = tr_their(fm, ft);
        let m2 = tr_my(fm, ft);
        // lengths after the first step: |d| - B + tgt
        assert(fits(ap(d, o), m2));
        assert(fits(ap(d, m), o2));
        lemma_tt_fit(ap(d, m), o2, q.drop_first());
        // TP1 on padded ops: ap(ap(d,o), m2) == ap(ap(d,m), o2)
        assert(ap(ap(d, o), m2) == ap(ap(d, ft), m2));
        let r = tt(o2, q.drop_first());
        let tail = r.1;
        assert(tt(o, q).1 == seq![m2].add(tail));
        assert(seq![m2].add(tail).drop_first() =~= tail);
        assert(seq![m2].add(tail)[0] == m2);
        assert(ap(ap(d, o), m2) == ap(ap(d, m), o2));
        assert(fold(ap(d, m), q.drop_first()) == fold(d, q));
    }
}

// ---------- the protocol invariant with lengths ----------
pub open spec fn inv2(w: W) -> bool {
    &&& inv(w)
    &&& chain_fits(w.srv.lc, w.srv.q)
    // the editor's pending edits fit the buffers they are applied to
    &&& chain_fits(fold(w.srv.lc, w.srv.q.subrange(0, w.ed.rd - confirmed(w.srv))), up_ops(w.up))
}

pub proof fn lemma_init2(content: Seq<char>)
    ensures inv2(W {
        srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
        ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() }),
{
    lemma_init(content);
    assert(up_ops(Seq::<Up>::empty()) =~= Seq::<int>::empty());
}

// a CRDT change: its op must fit the daemon's current text
pub proof fn lemma_crdt_step2(w: W, o: int)
    requires inv2(w),
    ensures inv2(crdt_step(w, o)),
{
    lemma_crdt_step(w, o);
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    lemma_chain_push(s.lc, s.q, o);
    assert(s.q.push(o).subrange(0, e.rd - c) =~= s.q.subrange(0, e.rd - c));
}

// the editor types an edit that fits its buffer
pub proof fn lemma_ed_local2(w: W, o: int)
    requires inv2(w), fits(w.ed.buf, o),
    ensures inv2(ed_local(w, o)),
{
    lemma_ed_local(w, o);
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let x = fold(s.lc, s.q.subrange(0, e.rd - c));
    assert(up_ops(ed_local(w, o).up) =~= up_ops(w.up).push(o));
    lemma_chain_push(x, up_ops(w.up), o);
}

// the daemon handles the editor's first pending edit
pub proof fn lemma_srv_recv2(w: W)
    requires inv2(w), w.up.len() > 0,
    ensures inv2(srv_recv(w)),
{
    lemma_srv_recv(w);
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let u = w.up[0];
    let k = (e.rd - c) as int;
    let lc1 = fold(s.lc, s.q.subrange(0, k));
    let q1 = s.q.subrange(k, s.q.len() as int);
    lemma_chain_split(s.lc, s.q, k);
    let ops = up_ops(w.up);
    assert(ops[0] == u.op);
    assert(fits(lc1, u.op));
    lemma_tt_fit(lc1, u.op, q1);
    let w2 = srv_recv(w);
    lemma_tt(lc1, u.op, q1);
    assert(u.rev == e.rd);
    assert(w2.srv.q == tt(u.op, q1).1);
    assert(w2.srv.q.len() == q1.len());
    assert(w2.srv.dr == s.dr);
    assert(w2.srv.lc == ap(lc1, u.op));
    assert(confirmed(w2.srv) == e.rd);
    assert(w2.srv.q.subrange(0, 0) =~= Seq::<int>::empty());
    assert(up_ops(w2.up) =~= ops.drop_first());
}

pub proof fn lemma_ed_recv2(w: W)
    requires inv2(w), w.down.len() > 0,
    ensures inv2(ed_recv(w)),
{
    lemma_ed_recv(w);
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let m = w.down[0];
    if m.rev == e.re {
        // accepted only with nothing in flight (see lemma_ed_recv)
        assert(w.up.len() == 0);
        assert(up_ops(w.up) =~= Seq::<int>::empty());
        assert(up_ops(ed_recv(w).up) =~= Seq::<int>::empty());
    }
}

// What the daemon relies on: the op it takes from an editor's edit, transformed over everything the
// editor had not seen, fits the daemon's current text (= the CRDT text), so the CRDT's
// `apply_delta_to_doc` and every other owner's `apply_crdt_change` cannot fail on length.
pub proof fn theorem_edit_out_fits(w: W)
    requires inv2(w), w.up.len() > 0,
    ensures fits(w.srv.cur, conc_edit_out(w)),
{
    let s = w.srv; let e = w.ed; let c = confirmed(s);
    let u = w.up[0];
    let k = (e.rd - c) as int;
    let lc1 = fold(s.lc, s.q.subrange(0, k));
    let q1 = s.q.subrange(k, s.q.len() as int);
    lemma_chain_split(s.lc, s.q, k);
    lemma_fold_split(s.lc, s.q, k);
    assert(up_ops(w.up)[0] == u.op);
    lemma_tt_fit(lc1, u.op, q1);
    assert(fold(lc1, q1) == s.cur);
}

// the op `edit_out` of daemon_proof.rs (restated here to keep this file independent)
pub open spec fn conc_edit_out(w: W) -> int {
    let u = w.up[0];
    let k = (u.rev - confirmed(w.srv)) as int;
    tt(u.op, w.srv.q.subrange(k, w.srv.q.len() as int)).0
}

// ---------- connection to ../boundary_proof ----------
// A sync message's text patches are `Splice(i, s)` / `DelSeq(i, n)` with `rep_ok(t, i, n)`
// (0 <= i, 0 <= n, i + n <= |t|) in boundary.rs's `step_view`; `replay(..) == Some(..)` there is the
// trusted fact that Automerge's patches replay on the previous visible text. The TextDelta the
// daemon builds from such a patch is retain(i) then delete(n) / insert(s): base length i + n.
// Hence a replayed patch fits the text it applies to.
pub open spec fn rep_ok(t: Seq<int>, i: int, n: int) -> bool { 0 <= i && 0 <= n && i + n <= t.len() }
pub proof fn lemma_patch_fits(t: Seq<char>, o: int, i: int, n: int)
    requires 0 <= i, 0 <= n, i + n <= t.len(), base_len_of(o) == i + n,
    ensures fits(t, o),
{}

} // verus!
fn main() {}
