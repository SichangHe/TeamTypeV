// Verus model: liveness of peer sync (Part A) and of daemon file writes (Part B), and their
// composition (Part C). See DESIGN.md. Trusted: uninterpreted `render`, `merge_res`, and one external_body
// axiom (`axiom_merge_unchanged`, Part B2).
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

// =====================================================================================
// Part A: peer sync. Changes are opaque ids. Directed edges e (src[e] -> dst[e]) are flattened.
// ch[p]   = set of changes in peer p's CRDT.
// bel[e]  = what src[e]'s sync state believes dst[e] has (shared heads + sent hashes).
// fl[e]   = sync messages in flight on edge e (FIFO, reliable), each a set of changes.
// ASSUMED protocol behaviour (stands for Automerge's generate/receive_sync_message):
//   gen(e): enabled iff ch[src] is not within bel[e]; sends ch[src] \ bel[e] and records it as believed.
//   rcv(e): delivers the oldest message; ch[dst] gains its changes.
// Edits have stopped: no change outside U is ever created (the set `u` is fixed).
// =====================================================================================
pub struct Net { pub ch: Seq<Set<nat>>, pub bel: Seq<Set<nat>>, pub fl: Seq<Seq<Set<nat>>> }

pub open spec fn topo_ok(n: nat, src: Seq<nat>, dst: Seq<nat>) -> bool {
    &&& src.len() == dst.len()
    &&& forall|e: int| 0 <= e < src.len() ==> (#[trigger] src[e]) < n && dst[e] < n
    // every edge has a reverse edge (a sync connection is bidirectional)
    &&& forall|e: int| #![trigger dst[e]] 0 <= e < src.len() ==> exists|r: int| 0 <= r < src.len() && src[r] == dst[e] && dst[r] == src[e]
}

// walk of edge indices from i to j
pub open spec fn path_ok(src: Seq<nat>, dst: Seq<nat>, p: Seq<nat>, i: nat, j: nat) -> bool
    decreases p.len(),
{
    if p.len() == 0 { i == j } else {
        p[0] < src.len() && src[p[0] as int] == i && path_ok(src, dst, p.drop_first(), dst[p[0] as int], j)
    }
}
pub open spec fn connected(n: nat, src: Seq<nat>, dst: Seq<nat>) -> bool {
    forall|i: nat, j: nat| i < n && j < n ==> #[trigger] reach(src, dst, i, j)
}
pub open spec fn reach(src: Seq<nat>, dst: Seq<nat>, i: nat, j: nat) -> bool { exists|p: Seq<nat>| path_ok(src, dst, p, i, j) }

pub open spec fn in_flight(m: Seq<Set<nat>>, x: nat) -> bool { exists|k: int| 0 <= k < m.len() && (#[trigger] m[k]).contains(x) }

pub open spec fn nwf(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, w: Net) -> bool {
    &&& w.ch.len() == n && w.bel.len() == src.len() && w.fl.len() == src.len()
    &&& forall|p: int| 0 <= p < n ==> (#[trigger] w.ch[p]).subset_of(u)
    &&& forall|e: int| 0 <= e < src.len() ==> (#[trigger] w.bel[e]).subset_of(u)
    &&& forall|e: int, k: int| 0 <= e < src.len() && 0 <= k < w.fl[e].len() ==> (#[trigger] w.fl[e][k]).subset_of(u)
    // belief is true or still in flight to the destination
    &&& forall|e: int, x: nat| 0 <= e < src.len() && #[trigger] w.bel[e].contains(x) ==>
            w.ch[dst[e] as int].contains(x) || in_flight(w.fl[e], x)
}

pub open spec fn gen_enabled(src: Seq<nat>, w: Net, e: int) -> bool {
    0 <= e < src.len() && !w.ch[src[e] as int].subset_of(w.bel[e])
}
pub open spec fn gen_step(src: Seq<nat>, w: Net, e: int) -> Net {
    Net { ch: w.ch,
          bel: w.bel.update(e, w.bel[e].union(w.ch[src[e] as int])),
          fl: w.fl.update(e, w.fl[e].push(w.ch[src[e] as int].difference(w.bel[e]))) }
}
pub open spec fn rcv_enabled(src: Seq<nat>, w: Net, e: int) -> bool { 0 <= e < src.len() && w.fl[e].len() > 0 }
pub open spec fn rcv_step(dst: Seq<nat>, w: Net, e: int) -> Net {
    Net { ch: w.ch.update(dst[e] as int, w.ch[dst[e] as int].union(w.fl[e][0])),
          bel: w.bel, fl: w.fl.update(e, w.fl[e].drop_first()) }
}
pub open spec fn net_step(src: Seq<nat>, dst: Seq<nat>, w: Net, w2: Net) -> bool {
    exists|e: int| (gen_enabled(src, w, e) && w2 == gen_step(src, w, e)) || (rcv_enabled(src, w, e) && w2 == rcv_step(dst, w, e))
}
pub open spec fn net_quiet(src: Seq<nat>, w: Net) -> bool {
    forall|e: int| 0 <= e < src.len() ==> !gen_enabled(src, w, e) && !rcv_enabled(src, w, e)
}

// ranks: A = total believed-missing, B = messages in flight
pub open spec fn rank_a(bel: Seq<Set<nat>>, u: Set<nat>, k: nat) -> nat
    decreases k,
{
    if k == 0 { 0 } else { (u.len() - bel[k - 1].len()) as nat + rank_a(bel, u, (k - 1) as nat) }
}
pub open spec fn rank_b(fl: Seq<Seq<Set<nat>>>, k: nat) -> nat
    decreases k,
{
    if k == 0 { 0 } else { fl[k - 1].len() + rank_b(fl, (k - 1) as nat) }
}

pub proof fn lemma_strict(a: Set<nat>, b: Set<nat>, x: nat, u: Set<nat>)
    requires a.subset_of(b), b.subset_of(u), b.contains(x), !a.contains(x),
    ensures a.len() < b.len(),
{
    lemma_len_subset(a.insert(x), b);
    assert(a.insert(x).len() == a.len() + 1);
}

pub proof fn lemma_rank_a_update(bel: Seq<Set<nat>>, u: Set<nat>, k: nat, e: int, b2: Set<nat>)
    requires
        k <= bel.len(), 0 <= e < bel.len(), b2.subset_of(u),
        forall|i: int| 0 <= i < bel.len() ==> (#[trigger] bel[i]).subset_of(u),
        bel[e].subset_of(b2),
    ensures
        rank_a(bel.update(e, b2), u, k) <= rank_a(bel, u, k),
        e < k && b2.len() > bel[e].len() ==> rank_a(bel.update(e, b2), u, k) < rank_a(bel, u, k),
    decreases k,
{
    if k > 0 {
        lemma_rank_a_update(bel, u, (k - 1) as nat, e, b2);
        lemma_len_subset(bel[k - 1], u);
        lemma_len_subset(b2, u);
        lemma_len_subset(bel[e], b2);
        if e == k - 1 {
            assert(bel.update(e, b2)[k - 1] == b2);
        } else {
            assert(bel.update(e, b2)[k - 1] == bel[k - 1]);
        }
    }
}

pub proof fn lemma_rank_b_update(fl: Seq<Seq<Set<nat>>>, k: nat, e: int, f2: Seq<Set<nat>>)
    requires k <= fl.len(), 0 <= e < fl.len(),
    ensures
        e < k ==> rank_b(fl.update(e, f2), k) + fl[e].len() == rank_b(fl, k) + f2.len(),
        e >= k ==> rank_b(fl.update(e, f2), k) == rank_b(fl, k),
    decreases k,
{
    if k > 0 {
        lemma_rank_b_update(fl, (k - 1) as nat, e, f2);
        if e == k - 1 { assert(fl.update(e, f2)[k - 1] == f2); }
        else { assert(fl.update(e, f2)[k - 1] == fl[k - 1]); }
    }
}

pub proof fn lemma_net_step(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, w: Net, w2: Net)
    requires topo_ok(n, src, dst), nwf(n, src, dst, u, w), net_step(src, dst, w, w2),
    ensures
        nwf(n, src, dst, u, w2),
        rank_a(w2.bel, u, src.len()) < rank_a(w.bel, u, src.len())
            || (rank_a(w2.bel, u, src.len()) == rank_a(w.bel, u, src.len())
                && rank_b(w2.fl, src.len()) < rank_b(w.fl, src.len())),
        forall|p: int| 0 <= p < n ==> (#[trigger] w.ch[p]).subset_of(w2.ch[p]),
{
    let e = choose|e: int| (gen_enabled(src, w, e) && w2 == gen_step(src, w, e)) || (rcv_enabled(src, w, e) && w2 == rcv_step(dst, w, e));
    if gen_enabled(src, w, e) && w2 == gen_step(src, w, e) {
        let s = w.ch[src[e] as int];
        let b2 = w.bel[e].union(s);
        assert(s.subset_of(u));
        assert(b2.subset_of(u));
        let x = choose|x: nat| s.contains(x) && !w.bel[e].contains(x);
        lemma_strict(w.bel[e], b2, x, u);
        lemma_rank_a_update(w.bel, u, src.len(), e, b2);
        lemma_rank_b_update(w.fl, src.len(), e, w.fl[e].push(s.difference(w.bel[e])));
        // nwf
        assert forall|e2: int, k: int| 0 <= e2 < src.len() && 0 <= k < w2.fl[e2].len() implies (#[trigger] w2.fl[e2][k]).subset_of(u) by {
            if e2 == e && k == w.fl[e].len() { assert(w2.fl[e2][k] == s.difference(w.bel[e])); }
            else if e2 == e { assert(w2.fl[e2][k] == w.fl[e][k]); }
            else { assert(w2.fl[e2][k] == w.fl[e2][k]); }
        }
        assert forall|e2: int, x2: nat| 0 <= e2 < src.len() && #[trigger] w2.bel[e2].contains(x2) implies
            w2.ch[dst[e2] as int].contains(x2) || in_flight(w2.fl[e2], x2) by {
            if e2 == e {
                if w.bel[e].contains(x2) {
                    if !w.ch[dst[e] as int].contains(x2) {
                        let k = choose|k: int| 0 <= k < w.fl[e].len() && w.fl[e][k].contains(x2);
                        assert(w2.fl[e][k] == w.fl[e][k]);
                    }
                } else {
                    assert(s.contains(x2));
                    let k = w.fl[e].len() as int;
                    assert(w2.fl[e][k] == s.difference(w.bel[e]));
                    assert(w2.fl[e][k].contains(x2));
                }
            } else {
                assert(w2.bel[e2] == w.bel[e2]);
                assert(w2.fl[e2] == w.fl[e2]);
            }
        }
    } else {
        let m = w.fl[e][0];
        assert(m.subset_of(u));
        let d = dst[e] as int;
        lemma_rank_b_update(w.fl, src.len(), e, w.fl[e].drop_first());
        assert(w2.bel == w.bel);
        assert forall|e2: int, k: int| 0 <= e2 < src.len() && 0 <= k < w2.fl[e2].len() implies (#[trigger] w2.fl[e2][k]).subset_of(u) by {
            if e2 == e { assert(w2.fl[e2][k] == w.fl[e][k + 1]); } else { assert(w2.fl[e2][k] == w.fl[e2][k]); }
        }
        assert forall|p: int| 0 <= p < n implies (#[trigger] w2.ch[p]).subset_of(u) by {
            if p == d { assert(w2.ch[p] == w.ch[d].union(m)); }
        }
        assert forall|p: int| 0 <= p < n implies (#[trigger] w.ch[p]).subset_of(w2.ch[p]) by {
            if p == d { assert(w2.ch[p] == w.ch[d].union(m)); }
        }
        assert forall|e2: int, x2: nat| 0 <= e2 < src.len() && #[trigger] w2.bel[e2].contains(x2) implies
            w2.ch[dst[e2] as int].contains(x2) || in_flight(w2.fl[e2], x2) by {
            assert(w.bel[e2].contains(x2));
            if w.ch[dst[e2] as int].contains(x2) {
                assert(w.ch[dst[e2] as int].subset_of(w2.ch[dst[e2] as int]));
            } else {
                let k = choose|k: int| 0 <= k < w.fl[e2].len() && w.fl[e2][k].contains(x2);
                if e2 == e {
                    if k == 0 { assert(w2.ch[d] == w.ch[d].union(m)); assert(dst[e2] as int == d); }
                    else { assert(w2.fl[e][k - 1] == w.fl[e][k]); }
                } else { assert(w2.fl[e2][k] == w.fl[e2][k]); }
            }
        }
    }
    assert forall|p: int| 0 <= p < n implies (#[trigger] w.ch[p]).subset_of(w2.ch[p]) by {
        if gen_enabled(src, w, e) && w2 == gen_step(src, w, e) { assert(w2.ch == w.ch); }
    }
}

// at quiescence, ch[src[e]] is within ch[dst[e]] for every edge
pub proof fn lemma_quiet_edge(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, w: Net, e: int)
    requires nwf(n, src, dst, u, w), net_quiet(src, w), 0 <= e < src.len(),
    ensures w.ch[src[e] as int].subset_of(w.ch[dst[e] as int]),
{
    assert(!gen_enabled(src, w, e));
    assert(w.ch[src[e] as int].subset_of(w.bel[e]));
    assert forall|x: nat| w.ch[src[e] as int].contains(x) implies w.ch[dst[e] as int].contains(x) by {
        assert(w.bel[e].contains(x));
        if !w.ch[dst[e] as int].contains(x) {
            assert(in_flight(w.fl[e], x));
            assert(w.fl[e].len() == 0);
        }
    }
}

pub proof fn lemma_path_subset(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, w: Net, p: Seq<nat>, i: nat, j: nat)
    requires nwf(n, src, dst, u, w), net_quiet(src, w), topo_ok(n, src, dst), path_ok(src, dst, p, i, j), i < n,
    ensures j < n, w.ch[i as int].subset_of(w.ch[j as int]),
    decreases p.len(),
{
    if p.len() > 0 {
        let e = p[0] as int;
        lemma_quiet_edge(n, src, dst, u, w, e);
        lemma_path_subset(n, src, dst, u, w, p.drop_first(), dst[e], j);
    }
}

// quiescent network over a connected topology: all peers hold the same changes
pub proof fn theorem_net_quiet_agrees(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, w: Net)
    requires topo_ok(n, src, dst), connected(n, src, dst), nwf(n, src, dst, u, w), net_quiet(src, w),
    ensures forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> w.ch[i] == w.ch[j],
{
    assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies w.ch[i] == w.ch[j] by {
        assert(reach(src, dst, i as nat, j as nat));
        assert(reach(src, dst, j as nat, i as nat));
        let p = choose|p: Seq<nat>| #[trigger] path_ok(src, dst, p, i as nat, j as nat);
        lemma_path_subset(n, src, dst, u, w, p, i as nat, j as nat);
        let q = choose|q: Seq<nat>| #[trigger] path_ok(src, dst, q, j as nat, i as nat);
        lemma_path_subset(n, src, dst, u, w, q, j as nat, i as nat);
        assert(w.ch[i] =~= w.ch[j]);
    }
}

// Liveness: every execution that keeps stepping while not quiescent reaches quiescence, in which
// all peers hold the same changes, and each peer holds every change any peer held at the start.
pub proof fn lemma_net_run_ends(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, f: spec_fn(nat) -> Net, i: nat)
    requires
        topo_ok(n, src, dst), nwf(n, src, dst, u, f(i)),
        forall|j: nat| j >= i && !net_quiet(src, #[trigger] f(j)) ==> net_step(src, dst, f(j), f(j + 1)),
    ensures
        exists|m: nat| #![trigger f(m)] m >= i && net_quiet(src, f(m)) && nwf(n, src, dst, u, f(m))
            && (forall|p: int| 0 <= p < n ==> (#[trigger] f(i).ch[p]).subset_of(f(m).ch[p])),
    decreases rank_a(f(i).bel, u, src.len()), rank_b(f(i).fl, src.len()),
{
    if net_quiet(src, f(i)) {
        assert forall|p: int| 0 <= p < n implies (#[trigger] f(i).ch[p]).subset_of(f(i).ch[p]) by {}
    } else {
        assert(net_step(src, dst, f(i), f(i + 1)));
        lemma_net_step(n, src, dst, u, f(i), f(i + 1));
        lemma_net_run_ends(n, src, dst, u, f, i + 1);
        let m = choose|m: nat| #![trigger f(m)] m >= i + 1 && net_quiet(src, f(m)) && nwf(n, src, dst, u, f(m))
            && (forall|p: int| 0 <= p < n ==> (#[trigger] f(i + 1).ch[p]).subset_of(f(m).ch[p]));
        assert forall|p: int| 0 <= p < n implies (#[trigger] f(i).ch[p]).subset_of(f(m).ch[p]) by {
            assert(f(i).ch[p].subset_of(f(i + 1).ch[p]));
            assert(f(i + 1).ch[p].subset_of(f(m).ch[p]));
        }
    }
}

// ---- connection loss and reconnect ----
// peer.rs: a lost/stalled connection ends its `SyncActor`; the initiator reconnects forever
// (`reconnect`, generation-checked), and every connection starts a fresh `SyncActor` with
// `AutomergeSyncState::new()`. Messages in flight on a dead connection are gone. So loss = reset of
// the edge: belief forgotten, nothing in flight, CRDT content (ch) untouched. (A reliable stream does not
// drop single messages, so loss without reset does not occur; ASSUMED.)
pub open spec fn reset_step(w: Net, e: int) -> Net {
    Net { ch: w.ch, bel: w.bel.update(e, Set::empty()), fl: w.fl.update(e, Seq::empty()) }
}
pub open spec fn any_step(src: Seq<nat>, dst: Seq<nat>, w: Net, w2: Net) -> bool {
    net_step(src, dst, w, w2) || exists|e: int| 0 <= e < src.len() && w2 == reset_step(w, e)
}

pub proof fn lemma_reset_wf(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, w: Net, e: int)
    requires nwf(n, src, dst, u, w), 0 <= e < src.len(),
    ensures nwf(n, src, dst, u, reset_step(w, e)),
{
    let w2 = reset_step(w, e);
    assert forall|e2: int, x: nat| 0 <= e2 < src.len() && #[trigger] w2.bel[e2].contains(x) implies
        w2.ch[dst[e2] as int].contains(x) || in_flight(w2.fl[e2], x) by {
        assert(e2 != e);
        assert(w2.bel[e2] == w.bel[e2]);
        assert(w2.fl[e2] == w.fl[e2]);
    }
    assert forall|e2: int, k: int| 0 <= e2 < src.len() && 0 <= k < w2.fl[e2].len() implies (#[trigger] w2.fl[e2][k]).subset_of(u) by {
        assert(e2 != e);
        assert(w2.fl[e2][k] == w.fl[e2][k]);
    }
}

// Liveness under finitely many connection losses: if from index `i0` on there are no more resets
// (the connection stays up), the run reaches a quiet state. Before `i0` any interleaving of steps and
// resets is allowed; `nwf` holds throughout.
pub proof fn lemma_prefix_nwf(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, f: spec_fn(nat) -> Net, i: nat)
    requires
        topo_ok(n, src, dst), nwf(n, src, dst, u, f(0)),
        forall|j: nat| j < i ==> any_step(src, dst, f(j), #[trigger] f(j + 1)),
    ensures nwf(n, src, dst, u, f(i)),
    decreases i,
{
    if i > 0 {
        lemma_prefix_nwf(n, src, dst, u, f, (i - 1) as nat);
        let j = (i - 1) as nat;
        assert(any_step(src, dst, f(j), f(j + 1)));
        if net_step(src, dst, f(j), f(j + 1)) {
            lemma_net_step(n, src, dst, u, f(j), f(j + 1));
        } else {
            let e = choose|e: int| 0 <= e < src.len() && f(j + 1) == #[trigger] reset_step(f(j), e);
            lemma_reset_wf(n, src, dst, u, f(j), e);
        }
    }
}

pub proof fn theorem_live_with_finite_resets(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, f: spec_fn(nat) -> Net, i0: nat)
    requires
        topo_ok(n, src, dst), connected(n, src, dst), nwf(n, src, dst, u, f(0)),
        forall|j: nat| j < i0 ==> any_step(src, dst, f(j), #[trigger] f(j + 1)),
        forall|j: nat| j >= i0 && !net_quiet(src, #[trigger] f(j)) ==> net_step(src, dst, f(j), f(j + 1)),
    ensures
        exists|m: nat| #![trigger f(m)] m >= i0 && net_quiet(src, f(m)) && nwf(n, src, dst, u, f(m))
            && (forall|p: int, q: int| 0 <= p < n && 0 <= q < n ==> (#[trigger] f(m).ch[p]) == (#[trigger] f(m).ch[q])),
{
    lemma_prefix_nwf(n, src, dst, u, f, i0);
    lemma_net_run_ends(n, src, dst, u, f, i0);
    let m = choose|m: nat| #![trigger f(m)] m >= i0 && net_quiet(src, f(m)) && nwf(n, src, dst, u, f(m))
        && (forall|p: int| 0 <= p < n ==> (#[trigger] f(i0).ch[p]).subset_of(f(m).ch[p]));
    theorem_net_quiet_agrees(n, src, dst, u, f(m));
}

// Non-vacuity: two peers, one change at peer 0. Gen then deliver reaches quiescence with both peers equal.
pub proof fn example_net()
    ensures ({
        let src = seq![0nat, 1nat]; let dst = seq![1nat, 0nat];
        let u = set![7nat];
        let w0 = Net { ch: seq![set![7nat], Set::<nat>::empty()], bel: seq![Set::<nat>::empty(), Set::<nat>::empty()],
                       fl: seq![Seq::<Set<nat>>::empty(), Seq::<Set<nat>>::empty()] };
        let w1 = gen_step(src, w0, 0);
        let w2 = rcv_step(dst, w1, 0);
        let w3 = gen_step(src, w2, 1);
        let w4 = rcv_step(dst, w3, 1);
        &&& nwf(2, src, dst, u, w0) && gen_enabled(src, w0, 0)
        &&& w4.ch[0] == w4.ch[1] && w4.ch[0].contains(7nat)
    }),
{
    let src = seq![0nat, 1nat]; let dst = seq![1nat, 0nat];
    let u = set![7nat];
    let w0 = Net { ch: seq![set![7nat], Set::<nat>::empty()], bel: seq![Set::<nat>::empty(), Set::<nat>::empty()],
                   fl: seq![Seq::<Set<nat>>::empty(), Seq::<Set<nat>>::empty()] };
    let w1 = gen_step(src, w0, 0);
    let w2 = rcv_step(dst, w1, 0);
    let w3 = gen_step(src, w2, 1);
    let w4 = rcv_step(dst, w3, 1);
    assert(nwf(2, src, dst, u, w0)) by {
        assert forall|e: int, x: nat| 0 <= e < 2 && #[trigger] w0.bel[e].contains(x) implies false by {}
    }
    assert(gen_enabled(src, w0, 0)) by { assert(w0.ch[0].contains(7nat)); assert(!w0.bel[0].contains(7nat)); }
    assert(w2.ch[1].contains(7nat)) by { assert(w1.fl[0][0].contains(7nat)); assert(w1.fl[0].len() == 1); }
    assert(w4.ch[0] =~= w4.ch[1]) by {
        assert(w2.ch[0] == w0.ch[0]);
        assert(w4.ch[0].contains(7nat));
        assert(w4.ch[1] == w2.ch[1]);
    }
}

// =====================================================================================
// Part B: one daemon's handling of one file it owns (no editor has it open), no outside writers.
// Contents are opaque values; None = file absent (written(m, None) stands for `remove_disk_file`, reached via
// sync patches `FileRemoval`; `write_file_now` itself does nothing for an absent file). daemon.rs names in brackets.
//   d   = bytes on disk                     r   = `disk_content` entry (last bytes the daemon saw/wrote)
//   def = path in `deferred_writes`         git = `git_running`
// c (not stored) = the CRDT's content for the file = render(changes).
// Steps (each is one actor message, atomic):
//   on_change(c, ok): the CRDT content changed [sync patch / edit / open] -> `write_file`:
//        git: deferred; else write (`try_write_file`): success d:=r:=c, def:=false; failure def:=true (fixed code).
//   git_start: git := true           git_finish: git := false
//   retry (`RescanFiles` after fix): if !git && def: write again.
// A watcher event / rescan reads the disk: it changes the CRDT iff `emits`.
// =====================================================================================
pub uninterp spec fn render(s: Set<nat>) -> Option<int>;   // ASSUMED: content is a function of the change set (automerge SEC)

pub struct Dm { pub d: Option<int>, pub r: Option<int>, pub def: bool, pub git: bool }

pub open spec fn inv_b(m: Dm, c: Option<int>) -> bool {
    &&& (m.r.is_some() ==> m.d == m.r)      // the daemon's record matches the disk (no outside writers)
    &&& (m.r.is_none() ==> m.d.is_none())
    &&& (!m.def ==> m.d == c)               // unless a write is pending, disk shows the CRDT
}
pub open spec fn written(m: Dm, c: Option<int>) -> Dm { Dm { d: c, r: c, def: false, git: m.git } }

pub open spec fn on_change(m: Dm, c2: Option<int>, ok: bool) -> Dm {
    if m.git || !ok { Dm { def: true, ..m } } else { written(m, c2) }
}
pub open spec fn git_start(m: Dm) -> Dm { Dm { git: true, ..m } }
// the real `finish_git` also retries deferred writes at once; the model leaves that to `retry` (weaker, sound)
pub open spec fn git_finish(m: Dm) -> Dm { Dm { git: false, ..m } }
pub open spec fn retry(m: Dm, c: Option<int>, ok: bool) -> Dm {
    if !m.git && m.def && ok { written(m, c) } else { m }
}

// does a watcher event or rescan make the daemon change the CRDT on its own?
// (file read as unchanged: no; file missing while the CRDT has it: deletion unless a write is pending)
pub open spec fn emits(m: Dm, c: Option<int>) -> bool {
    !m.git && ((m.d.is_none() && c.is_some() && !m.def) || (m.d.is_some() && m.r != m.d))
}

pub proof fn lemma_b_init(c: Option<int>)
    ensures inv_b(Dm { d: c, r: c, def: false, git: false }, c),
{}
pub proof fn lemma_b_on_change(m: Dm, c: Option<int>, c2: Option<int>, ok: bool)
    requires inv_b(m, c), ensures inv_b(on_change(m, c2, ok), c2),
{}
pub proof fn lemma_b_git_start(m: Dm, c: Option<int>) requires inv_b(m, c), ensures inv_b(git_start(m), c) {}
pub proof fn lemma_b_git_finish(m: Dm, c: Option<int>) requires inv_b(m, c), ensures inv_b(git_finish(m), c) {}
pub proof fn lemma_b_retry(m: Dm, c: Option<int>, ok: bool) requires inv_b(m, c), ensures inv_b(retry(m, c, ok), c) {}

// echo-freedom: the daemon's own writes, failed writes and deferrals never make a watcher event
// or rescan change the CRDT, so the set of changes stays closed (Part A's `u` is fixed).
pub proof fn theorem_no_echo(m: Dm, c: Option<int>)
    requires inv_b(m, c),
    ensures !emits(m, c),
{}

// settling: once edits stop, git finishes, and a retry succeeds, the disk shows the CRDT.
pub proof fn theorem_settles(m: Dm, c: Option<int>) -> (m2: Dm)
    requires inv_b(m, c),
    ensures inv_b(m2, c), !m2.def, !m2.git, m2.d == c,
{
    let m1 = git_finish(m);
    lemma_b_git_finish(m, c);
    lemma_b_retry(m1, c, true);
    retry(m1, c, true)
}

// Non-vacuity of the failure path: a failed write leaves a pending write, and disk differs from the CRDT.
pub proof fn example_failed_write()
    ensures ({
        let m0 = Dm { d: None, r: None, def: false, git: false };
        let m1 = on_change(m0, Some(5int), false);
        inv_b(m0, None) && inv_b(m1, Some(5int)) && m1.def && m1.d != Some(5int) && !emits(m1, Some(5int))
    }),
{}

// =====================================================================================
// Part B2: the Git path. While `git_running`, watcher events and rescans are ignored, writes and
// removals are deferred, and Git (an OUTSIDE writer) may change the disk arbitrarily. `finish_git`
// then (1) performs deferred removals whose file is still absent from the CRDT, (2) rescans: a disk
// that differs from the record is merged into the CRDT (a new change: the only echo allowed, once per
// run), (3) retries deferred writes (here: `retry`).
// ASSUMED (`merge_disk_content`): merging an outside edit into an unchanged shared text yields the
// outside text (the OT three-way merge with base == shared); same axiom as daemon_proof's disk_proof.
// Holds in `merge_disk_content` for OWNED files (string: empty shared diff, transform is identity;
// binary or no base: the disk bytes are taken). Unowned files go through `remove_file`'s editor path,
// outside this model.
// =====================================================================================
pub struct Gm { pub d: Option<int>, pub r: Option<int>, pub def: bool, pub rem: bool, pub git: bool }

pub uninterp spec fn merge_res(r: Option<int>, c: Option<int>, d: Option<int>) -> Option<int>;
#[verifier::external_body]
pub proof fn axiom_merge_unchanged(b: Option<int>, d: Option<int>)
    ensures merge_res(b, b, d) == d,
{}

// invariant while Git runs: only the record/CRDT relation survives the outside writer
pub open spec fn inv_g(m: Gm, c: Option<int>) -> bool {
    &&& (!m.git ==> (m.r.is_some() ==> m.d == m.r) && (m.r.is_none() ==> m.d.is_none()))
    &&& (!m.def && !m.rem ==> m.r == c)
    &&& (m.rem && !m.def ==> c.is_none())   // a deferred removal is the CRDT's pending change
    &&& (!m.git ==> !m.rem)
    &&& (!m.git && !m.def ==> m.d == c)
}
// the CRDT changes while a sync/edit arrives: write (not git) or deferral (git); a removal in the
// CRDT while git runs is deferred (`deferred_removals`), otherwise it removes the disk file
pub open spec fn g_change(m: Gm, c2: Option<int>, ok: bool) -> Gm {
    // daemon.rs: a removal while git runs goes ONLY to `deferred_removals`; a write to `deferred_writes`
    if m.git { if c2.is_none() { Gm { rem: true, ..m } } else { Gm { def: true, ..m } } }
    else if ok { Gm { d: c2, r: c2, def: false, rem: false, ..m } }
    else { Gm { def: true, ..m } }
}
pub open spec fn g_start(m: Gm) -> Gm { Gm { git: true, ..m } }
// Git changes the disk (any content) while it runs
pub open spec fn g_outside(m: Gm, d2: Option<int>) -> Gm { Gm { d: d2, ..m } }

// finish_git: returns the daemon state and the new CRDT content (possibly one new change)
pub open spec fn g_finish(m: Gm, c: Option<int>) -> (Gm, Option<int>) {
    // (1) deferred removal
    let m1 = if m.rem && c.is_none() { Gm { d: None, r: None, rem: false, ..m } } else { Gm { rem: false, ..m } };
    // (2) rescan merges a disk that differs from the record
    if m1.d != m1.r {
        let c2 = merge_res(m1.r, c, m1.d);
        // record := disk; a pending write (def) keeps the file pending
        (Gm { r: m1.d, git: false, ..m1 }, c2)
    } else {
        (Gm { git: false, ..m1 }, c)
    }
}
// (3) retry of the deferred write (ASSUMED to succeed eventually; `run` retries every 5 s)
pub open spec fn g_retry(m: Gm, c: Option<int>, ok: bool) -> Gm {
    if !m.git && m.def && ok { Gm { d: c, r: c, def: false, ..m } } else { m }
}

pub proof fn lemma_g_change(m: Gm, c: Option<int>, c2: Option<int>, ok: bool)
    requires inv_g(m, c), ensures inv_g(g_change(m, c2, ok), c2),
{}
pub proof fn lemma_g_start(m: Gm, c: Option<int>) requires inv_g(m, c), ensures inv_g(g_start(m), c) {}
// Git changes the disk, nothing else: the invariant for a running Git (git == true) survives
pub proof fn lemma_g_outside(m: Gm, c: Option<int>, d2: Option<int>) requires inv_g(m, c), m.git, ensures inv_g(g_outside(m, d2), c) {}

// finish_git re-establishes the full invariant for the (possibly merged) CRDT content, so after a
// run the daemon is back in Part B's state: at most one change was introduced.
pub proof fn lemma_g_finish(m: Gm, c: Option<int>)
    requires inv_g(m, c), m.git,
    ensures ({
        let r = g_finish(m, c);
        // the disk diverges from the CRDT only with a pending write; the record equals the disk
        &&& !r.0.git && (r.0.r.is_some() ==> r.0.d == r.0.r) && (r.0.r.is_none() ==> r.0.d.is_none())
        &&& (!r.0.def ==> r.0.d == r.1)
        &&& (!r.0.def ==> r.0.r == r.1)
        // no outside change => no new CRDT change
        &&& (m.d == m.r && !(m.rem && c.is_none()) ==> r.1 == c)
    }),
{
    let r = g_finish(m, c);
    if !m.def {
        // record == c, so an outside change merges to exactly the disk
        axiom_merge_unchanged(c, m.d);
    }
}

// a retry that fails keeps the invariant; one that succeeds settles (theorem below needs one success)
pub proof fn lemma_g_retry(m: Gm, c: Option<int>, ok: bool)
    requires inv_g(m, c), !m.git,
    ensures inv_g(g_retry(m, c, ok), c), ok ==> !g_retry(m, c, ok).def && g_retry(m, c, ok).d == c,
{}

pub proof fn theorem_git_settles(m: Gm, c: Option<int>) -> (r: (Gm, Option<int>))
    requires inv_g(m, c), m.git,
    ensures
        // the result is the model's run, not any state that happens to satisfy the rest
        r == (g_retry(g_finish(m, c).0, g_finish(m, c).1, true), g_finish(m, c).1),
        inv_g(r.0, r.1), !r.0.def, !r.0.git, r.0.d == r.1,
{
    lemma_g_finish(m, c);
    let f = g_finish(m, c);
    let m3 = g_retry(f.0, f.1, true);
    assert(inv_g(m3, f.1));
    (m3, f.1)
}

// B2 witnesses (against vacuity): the requires are satisfiable and the outside edit / deferred
// removal paths are taken.
pub proof fn example_git_outside_edit() {
    let m = Gm { d: Some(5), r: Some(1), def: false, rem: false, git: true };
    lemma_g_finish(m, Some(1));
    axiom_merge_unchanged(Some(1), Some(5));
    let f = g_finish(m, Some(1));
    assert(f.1 == Some(5) && f.0.d == Some(5) && f.0.r == Some(5) && !f.0.git);
    let r = theorem_git_settles(m, Some(1));
    assert(r.0.d == Some(5));
}
pub proof fn example_git_deferred_removal() {
    // a peer removed the file while Git ran and Git rewrote it; finish removes it again
    let m = Gm { d: Some(3), r: Some(1), def: false, rem: true, git: true };
    let r = theorem_git_settles(m, None);
    assert(g_finish(m, None).0.d.is_none());
    assert(r.1.is_none() && r.0.d.is_none());
}
pub proof fn example_git_pending_write_merged() {
    // a peer's change was deferred while Git also edited the file: both reach the CRDT
    let m = Gm { d: Some(7), r: Some(1), def: true, rem: false, git: true };
    let r = theorem_git_settles(m, Some(2));
    assert(r.0.d == merge_res(Some(1), Some(2), Some(7)));
}

// =====================================================================================
// Part C: composition. n daemons over a connected topology, quiescent network (Part A), every daemon's
// content is render of its change set (assumed), no pending writes. Then every owned file has the
// same bytes on every disk.
// =====================================================================================
pub proof fn theorem_pipeline(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, w: Net, dms: Seq<Dm>)
    requires
        topo_ok(n, src, dst), connected(n, src, dst), nwf(n, src, dst, u, w), net_quiet(src, w),
        dms.len() == n,
        forall|p: int| 0 <= p < n ==> inv_b(#[trigger] dms[p], render(w.ch[p])),
        forall|p: int| 0 <= p < n ==> !(#[trigger] dms[p]).def,
    ensures
        forall|p: int, q: int| 0 <= p < n && 0 <= q < n ==> (#[trigger] dms[p]).d == (#[trigger] dms[q]).d,
{
    theorem_net_quiet_agrees(n, src, dst, u, w);
    assert forall|p: int, q: int| 0 <= p < n && 0 <= q < n implies (#[trigger] dms[p]).d == (#[trigger] dms[q]).d by {
        assert(w.ch[p] == w.ch[q]);
    }
}

// ---- joint system: a network step that delivers changes to peer p also runs that daemon's write ----
pub struct J { pub net: Net, pub dms: Seq<Dm> }
pub open spec fn jinv(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, j: J) -> bool {
    nwf(n, src, dst, u, j.net) && j.dms.len() == n
    && forall|p: int| 0 <= p < n ==> inv_b(#[trigger] j.dms[p], render(j.net.ch[p]))
}
// a receive on edge e: the destination daemon's content changes, so `on_change` runs (write may fail)
pub open spec fn jrcv(dst: Seq<nat>, j: J, e: int, ok: bool) -> J {
    let w2 = rcv_step(dst, j.net, e);
    let d = dst[e] as int;
    J { net: w2, dms: j.dms.update(d, on_change(j.dms[d], render(w2.ch[d]), ok)) }
}
pub proof fn lemma_jrcv(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, j: J, e: int, ok: bool)
    requires topo_ok(n, src, dst), jinv(n, src, dst, u, j), rcv_enabled(src, j.net, e),
    ensures jinv(n, src, dst, u, jrcv(dst, j, e, ok)),
{
    let w2 = rcv_step(dst, j.net, e);
    lemma_net_step(n, src, dst, u, j.net, w2);
    let j2 = jrcv(dst, j, e, ok);
    let d = dst[e] as int;
    assert forall|p: int| 0 <= p < n implies inv_b(#[trigger] j2.dms[p], render(j2.net.ch[p])) by {
        if p == d { lemma_b_on_change(j.dms[d], render(j.net.ch[d]), render(w2.ch[d]), ok); }
        else { assert(j2.dms[p] == j.dms[p]); assert(w2.ch[p] == j.net.ch[p]); }
    }
}
// settle: every daemon's retry succeeds (git finished) => all disks show their CRDT
pub open spec fn jsettle(j: J) -> J {
    J { net: j.net, dms: Seq::new(j.dms.len(), |p: int| retry(git_finish(j.dms[p]), render(j.net.ch[p]), true)) }
}
pub proof fn theorem_pipeline_joint(n: nat, src: Seq<nat>, dst: Seq<nat>, u: Set<nat>, j: J)
    requires
        topo_ok(n, src, dst), connected(n, src, dst), jinv(n, src, dst, u, j), net_quiet(src, j.net),
    ensures ({
        let s = jsettle(j);
        &&& jinv(n, src, dst, u, s)
        &&& forall|p: int| 0 <= p < n ==> !(#[trigger] s.dms[p]).def && s.dms[p].d == render(j.net.ch[p])
        &&& forall|p: int, q: int| 0 <= p < n && 0 <= q < n ==> (#[trigger] s.dms[p]).d == (#[trigger] s.dms[q]).d
    }),
{
    let s = jsettle(j);
    theorem_net_quiet_agrees(n, src, dst, u, j.net);
    assert forall|p: int| 0 <= p < n implies inv_b(#[trigger] s.dms[p], render(j.net.ch[p])) by {
        lemma_b_git_finish(j.dms[p], render(j.net.ch[p]));
        lemma_b_retry(git_finish(j.dms[p]), render(j.net.ch[p]), true);
    }
    assert forall|p: int, q: int| 0 <= p < n && 0 <= q < n implies (#[trigger] s.dms[p]).d == (#[trigger] s.dms[q]).d by {
        assert(j.net.ch[p] == j.net.ch[q]);
    }
}

} // verus!
fn main() {}
