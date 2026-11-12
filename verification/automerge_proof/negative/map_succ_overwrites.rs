// Verus model of Automerge's map-register layer (the `files` map: put / delete / conflicts)
// with INCREMENTAL op application. See CRDT_NOTES.md. Self-contained (vstd only).
//
// Real mechanism being modelled (vendor/automerge-0.10.0/src):
//  - an applied op is stored with a `succ` list; applying op X with predecessors P adds X.id to the
//    succ of every p in P:  op_set2/change/batch.rs:68-76 (`handle_doc_op`: for each pending
//    (id, inc) in pred.remove(&doc_op.id) { succ.push(doc_op.add_succ(id, inc)) })
//    and op_set2/op_set.rs:245 (`add_succ` splices the succ columns of the pred op).
//  - an op is visible iff its succ list is empty:  op_set2/op_set.rs:650
//    (`if op.succ().len() == 0 && op.action != Action::Mark { ops.push(op) }`).
//  - a delete is an op with no value whose pred is the deleted op(s); conflicts = several visible
//    ops on one key (winner = greatest OpId, types.rs OpId ordering (counter, actor)).
// Objects are independent: `key` below stands for the pair (object id, map key).
use vstd::prelude::*;

verus! {

pub type Id = (nat, nat); // OpId = (counter, actor index)

pub open spec fn idlt(a: Id, b: Id) -> bool {
    a.0 < b.0 || (a.0 == b.0 && a.1 < b.1)
}

pub struct Op {
    pub id: Id,
    pub key: nat,
    pub pred: ISet<Id>,
    pub val: Option<nat>, // None = delete
}

pub struct Entry {
    pub op: Op,
    pub succ: ISet<Id>,
}

pub type State = IMap<Id, Entry>;

pub open spec fn empty_state() -> State {
    IMap::empty()
}

// incremental application (model of handle_doc_op/add_succ for one op in causal order)
pub open spec fn apply(s: State, op: Op) -> State {
    IMap::new(
        |id: Id| s.dom().contains(id) || id == op.id,
        |id: Id|
            if id == op.id {
                Entry { op: op, succ: ISet::empty() }
            } else if op.pred.contains(id) {
                Entry { op: s[id].op, succ: ISet::empty().insert(op.id) }
            } else {
                s[id]
            },
    )
}

// delivery history: causally valid = ids distinct, every pred was delivered earlier
pub open spec fn valid(h: Seq<Op>) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < h.len() ==> h[i].id != h[j].id
    &&& forall|i: int, p: Id| 0 <= i < h.len() && h[i].pred.contains(p) ==> exists|j: int| 0 <= j < i && #[trigger] h[j].id == p
}

pub open spec fn run(h: Seq<Op>) -> State
    decreases h.len(),
{
    if h.len() == 0 { empty_state() } else { apply(run(h.drop_last()), h.last()) }
}

// canonical state of an op set (order-free definition)
pub open spec fn has_id(s: ISet<Op>, id: Id) -> bool {
    exists|o: Op| s.contains(o) && o.id == id
}

pub open spec fn canon(s: ISet<Op>) -> State {
    IMap::new(
        |id: Id| has_id(s, id),
        |id: Id| Entry {
            op: choose|o: Op| s.contains(o) && o.id == id,
            succ: ISet::new(|x: Id| exists|o: Op| s.contains(o) && o.id == x && o.pred.contains(id)),
        },
    )
}

pub open spec fn ops_of(h: Seq<Op>) -> ISet<Op> {
    ISet::new(|o: Op| h.contains(o))
}

// ids unique in the set
pub open spec fn uniq(s: ISet<Op>) -> bool {
    forall|a: Op, b: Op| s.contains(a) && s.contains(b) && a.id == b.id ==> a == b
}

proof fn lemma_valid_prefix(h: Seq<Op>)
    requires h.len() > 0, valid(h),
    ensures valid(h.drop_last()),
{
    let g = h.drop_last();
    assert forall|i: int, j: int| 0 <= i < j < g.len() implies g[i].id != g[j].id by {
        assert(g[i] == h[i]);
        assert(g[j] == h[j]);
    }
    assert forall|i: int, p: Id| 0 <= i < g.len() && g[i].pred.contains(p) implies exists|j: int| 0 <= j < i && #[trigger] g[j].id == p by {
        assert(g[i] == h[i]);
        let j = choose|j: int| 0 <= j < i && #[trigger] h[j].id == p;
        assert(g[j] == h[j]);
    }
}

proof fn lemma_ops_push(h: Seq<Op>, o: Op)
    ensures ops_of(h.push(o)) == ops_of(h).insert(o),
{
    assert forall|x: Op| ops_of(h.push(o)).contains(x) == ops_of(h).insert(o).contains(x) by {
        assert(h.push(o).contains(x) == (h.contains(x) || x == o)) by {
            if x == o { assert(h.push(o)[h.len() as int] == x); }
            else if h.push(o).contains(x) {
                let i = choose|i: int| 0 <= i < h.push(o).len() && h.push(o)[i] == x;
                assert(i < h.len());
                assert(h[i] == x);
            }
            if h.contains(x) {
                let i = choose|i: int| 0 <= i < h.len() && h[i] == x;
                assert(h.push(o)[i] == x);
            }
        }
    }
    assert(ops_of(h.push(o)) =~= ops_of(h).insert(o));
}

proof fn lemma_uniq_h(h: Seq<Op>)
    requires valid(h),
    ensures uniq(ops_of(h)),
{
    assert forall|a: Op, b: Op| ops_of(h).contains(a) && ops_of(h).contains(b) && a.id == b.id implies a == b by {
        let i = choose|i: int| 0 <= i < h.len() && h[i] == a;
        let j = choose|j: int| 0 <= j < h.len() && h[j] == b;
        if i != j {
            if i < j { assert(h[i].id != h[j].id); } else { assert(h[j].id != h[i].id); }
        }
    }
}

// every pred of an op in the history is an id of an earlier op; hence no earlier op names op.id
proof fn lemma_step_facts(h: Seq<Op>)
    requires h.len() > 0, valid(h),
    ensures
        ({
            let g = h.drop_last();
            let op = h.last();
            &&& !has_id(ops_of(g), op.id)
            &&& forall|o: Op| ops_of(g).contains(o) ==> !o.pred.contains(op.id)
            &&& forall|p: Id| op.pred.contains(p) ==> has_id(ops_of(g), p)
            &&& !op.pred.contains(op.id)
        }),
{
    let g = h.drop_last();
    let op = h.last();
    let n = h.len() - 1;
    assert(h[n] == op);
    assert forall|o: Op| ops_of(g).contains(o) implies o.id != op.id by {
        let i = choose|i: int| 0 <= i < g.len() && g[i] == o;
        assert(h[i] == o);
        assert(h[i].id != h[n].id);
    }
    assert(!has_id(ops_of(g), op.id));
    assert forall|o: Op| ops_of(g).contains(o) implies !o.pred.contains(op.id) by {
        let i = choose|i: int| 0 <= i < g.len() && g[i] == o;
        assert(h[i] == o);
        if o.pred.contains(op.id) {
            let j = choose|j: int| 0 <= j < i && #[trigger] h[j].id == op.id;
            assert(h[j].id != h[n].id);
        }
    }
    assert forall|p: Id| op.pred.contains(p) implies has_id(ops_of(g), p) by {
        let j = choose|j: int| 0 <= j < n && #[trigger] h[j].id == p;
        assert(g[j] == h[j]);
        assert(ops_of(g).contains(g[j]));
    }
}

// MAIN STEP: incremental apply of a causally ready op equals the canonical state of the bigger set.
proof fn lemma_apply_canon(s: ISet<Op>, op: Op)
    requires
        uniq(s),
        !has_id(s, op.id),
        forall|o: Op| s.contains(o) ==> !o.pred.contains(op.id),
        forall|p: Id| op.pred.contains(p) ==> has_id(s, p),
        !op.pred.contains(op.id),
    ensures
        apply(canon(s), op) == canon(s.insert(op)),
{
    let s2 = s.insert(op);
    let a = apply(canon(s), op);
    let c = canon(s2);
    assert(a.dom() =~= c.dom()) by {
        assert forall|id: Id| a.dom().contains(id) == c.dom().contains(id) by {
            if id == op.id { assert(s2.contains(op)); assert(has_id(s2, id)); }
            if has_id(s, id) {
                let o = choose|o: Op| s.contains(o) && o.id == id;
                assert(s2.contains(o));
                assert(has_id(s2, id));
            }
            if has_id(s2, id) && id != op.id {
                let o = choose|o: Op| s2.contains(o) && o.id == id;
                assert(s.contains(o));
            }
        }
    }
    assert forall|id: Id| a.dom().contains(id) implies a[id] == c[id] by {
        if id == op.id {
            // op part
            assert(s2.contains(op));
            let o2 = choose|o: Op| s2.contains(o) && o.id == id;
            if o2 != op { assert(s.contains(o2)); assert(has_id(s, op.id)); }
            assert(c[id].op == op);
            assert(c[id].succ =~= ISet::<Id>::empty()) by {
                assert forall|x: Id| !c[id].succ.contains(x) by {
                    if c[id].succ.contains(x) {
                        let o = choose|o: Op| s2.contains(o) && o.id == x && o.pred.contains(id);
                        if o == op { assert(false); } else { assert(s.contains(o)); assert(false); }
                    }
                }
            }
        } else {
            let o1 = choose|o: Op| s.contains(o) && o.id == id;
            assert(s2.contains(o1));
            let o2 = choose|o: Op| s2.contains(o) && o.id == id;
            if o2 == op { assert(false); }
            assert(s.contains(o2));
            assert(o1 == o2);
            assert(canon(s)[id].op == o1);
            assert(c[id].op == o1);
            // succ
            assert(c[id].succ =~= a[id].succ) by {
                assert forall|x: Id| c[id].succ.contains(x) == a[id].succ.contains(x) by {
                    if c[id].succ.contains(x) {
                        let o = choose|o: Op| s2.contains(o) && o.id == x && o.pred.contains(id);
                        if o == op {
                            assert(op.pred.contains(id));
                        } else {
                            assert(s.contains(o));
                            assert(canon(s)[id].succ.contains(x));
                        }
                    }
                    if a[id].succ.contains(x) {
                        if op.pred.contains(id) && x == op.id {
                            assert(s2.contains(op));
                        } else {
                            assert(canon(s)[id].succ.contains(x));
                            let o = choose|o: Op| s.contains(o) && o.id == x && o.pred.contains(id);
                            assert(s2.contains(o));
                        }
                    }
                }
            }
            assert(a[id] == c[id]);
        }
    }
    assert(a =~= c);
}

// THEOREM 1: running any causally valid delivery history incrementally gives the canonical state
// of the set of ops delivered.
pub proof fn theorem_run_is_canon(h: Seq<Op>)
    requires valid(h),
    ensures run(h) == canon(ops_of(h)),
    decreases h.len(),
{
    if h.len() == 0 {
        assert(ops_of(h) =~= ISet::<Op>::empty());
        assert(canon(ops_of(h)) =~= empty_state()) by {
            assert(canon(ops_of(h)).dom() =~= ISet::<Id>::empty()) by {
                assert forall|id: Id| !has_id(ops_of(h), id) by {}
            }
        }
    } else {
        lemma_valid_prefix(h);
        let g = h.drop_last();
        theorem_run_is_canon(g);
        lemma_step_facts(h);
        lemma_uniq_h(g);
        lemma_apply_canon(ops_of(g), h.last());
        lemma_ops_push(g, h.last());
        assert(g.push(h.last()) =~= h);
    }
}

// THEOREM 2 (strong eventual consistency of the map layer): two causally valid delivery orders of
// the same set of ops yield identical incremental states.
pub proof fn theorem_sec_map(h1: Seq<Op>, h2: Seq<Op>)
    requires valid(h1), valid(h2), ops_of(h1) =~= ops_of(h2),
    ensures run(h1) == run(h2),
{
    theorem_run_is_canon(h1);
    theorem_run_is_canon(h2);
}

// ---- derived reads: visible values per key and the conflict winner ----
pub open spec fn visible_ids(s: State, key: nat) -> ISet<Id> {
    ISet::new(|id: Id| s.dom().contains(id) && s[id].op.key == key && s[id].succ.is_empty() && s[id].op.val.is_some())
}

pub open spec fn is_winner(s: State, key: nat, w: Id) -> bool {
    visible_ids(s, key).contains(w) && forall|x: Id| visible_ids(s, key).contains(x) && x != w ==> idlt(x, w)
}

pub proof fn corollary_visible_equal(h1: Seq<Op>, h2: Seq<Op>, key: nat)
    requires valid(h1), valid(h2), ops_of(h1) =~= ops_of(h2),
    ensures
        visible_ids(run(h1), key) == visible_ids(run(h2), key),
        forall|w: Id| is_winner(run(h1), key, w) == is_winner(run(h2), key, w),
{
    theorem_sec_map(h1, h2);
}

// ---- reachability / non-vacuity: concurrent puts (conflict) and a delete, two delivery orders ----
pub open spec fn pa() -> Op { Op { id: (1, 1), key: 7, pred: ISet::empty(), val: Some(10) } }   // actor 1 put
pub open spec fn pb() -> Op { Op { id: (1, 2), key: 7, pred: ISet::empty(), val: Some(20) } }   // actor 2 concurrent put
pub open spec fn dc() -> Op { Op { id: (2, 3), key: 7, pred: ISet::empty().insert((1, 1)), val: None } } // actor 3 deletes pa

pub proof fn example_run()
    ensures
        valid(seq![pa(), pb(), dc()]),
        valid(seq![pb(), pa(), dc()]),
        valid(seq![pa(), dc(), pb()]),
        run(seq![pa(), pb(), dc()]) == run(seq![pb(), pa(), dc()]),
        run(seq![pa(), pb(), dc()]) == run(seq![pa(), dc(), pb()]),
        // after pa and pb only: both visible (conflict), winner is the greater id
        visible_ids(run(seq![pa(), pb()]), 7) == ISet::<Id>::empty().insert((1, 1)).insert((1, 2)),
        is_winner(run(seq![pa(), pb()]), 7, (1, 2)),
        // after the delete: only pb visible
        visible_ids(run(seq![pa(), pb(), dc()]), 7) == ISet::<Id>::empty().insert((1, 2)),
{
    let h1 = seq![pa(), pb(), dc()];
    let h2 = seq![pb(), pa(), dc()];
    let h3 = seq![pa(), dc(), pb()];
    assert(valid(h1)) by {
        assert forall|i: int, p: Id| 0 <= i < h1.len() && h1[i].pred.contains(p) implies exists|j: int| 0 <= j < i && #[trigger] h1[j].id == p by {
            if i == 2 { assert(h1[0].id == p); }
        }
    }
    assert(valid(h2)) by {
        assert forall|i: int, p: Id| 0 <= i < h2.len() && h2[i].pred.contains(p) implies exists|j: int| 0 <= j < i && #[trigger] h2[j].id == p by {
            if i == 2 { assert(h2[1].id == p); }
        }
    }
    assert(valid(h3)) by {
        assert forall|i: int, p: Id| 0 <= i < h3.len() && h3[i].pred.contains(p) implies exists|j: int| 0 <= j < i && #[trigger] h3[j].id == p by {
            if i == 1 { assert(h3[0].id == p); }
        }
    }
    assert(ops_of(h1) =~= ops_of(h2)) by {
        assert forall|o: Op| ops_of(h1).contains(o) == ops_of(h2).contains(o) by {
            assert(h1.contains(o) ==> o == pa() || o == pb() || o == dc()) by {
                if h1.contains(o) { let i = choose|i: int| 0 <= i < 3 && h1[i] == o; }
            }
            assert(h2.contains(o) ==> o == pa() || o == pb() || o == dc()) by {
                if h2.contains(o) { let i = choose|i: int| 0 <= i < 3 && h2[i] == o; }
            }
            assert(h1[0] == pa() && h1[1] == pb() && h1[2] == dc());
            assert(h2[0] == pb() && h2[1] == pa() && h2[2] == dc());
        }
    }
    assert(ops_of(h1) =~= ops_of(h3)) by {
        assert forall|o: Op| ops_of(h1).contains(o) == ops_of(h3).contains(o) by {
            assert(h1.contains(o) ==> o == pa() || o == pb() || o == dc()) by {
                if h1.contains(o) { let i = choose|i: int| 0 <= i < 3 && h1[i] == o; }
            }
            assert(h3.contains(o) ==> o == pa() || o == pb() || o == dc()) by {
                if h3.contains(o) { let i = choose|i: int| 0 <= i < 3 && h3[i] == o; }
            }
            assert(h1[0] == pa() && h1[1] == pb() && h1[2] == dc());
            assert(h3[0] == pa() && h3[1] == dc() && h3[2] == pb());
        }
    }
    theorem_sec_map(h1, h2);
    theorem_sec_map(h1, h3);
    // concrete reads
    let g = seq![pa(), pb()];
    let s0 = apply(empty_state(), pa());
    let s1 = apply(s0, pb());
    assert(g.drop_last() =~= seq![pa()]);
    assert(seq![pa()].drop_last() =~= Seq::<Op>::empty());
    assert(run(Seq::<Op>::empty()) == empty_state());
    assert(seq![pa()].drop_last() =~= Seq::<Op>::empty());
    assert(seq![pa()].last() == pa());
    assert(run(seq![pa()]) == s0);
    assert(run(g) == s1);
    assert(s1[(1, 1)].succ =~= ISet::<Id>::empty());
    assert(s1[(1, 2)].succ =~= ISet::<Id>::empty());
    assert(visible_ids(s1, 7) =~= ISet::<Id>::empty().insert((1, 1)).insert((1, 2)));
    assert(is_winner(s1, 7, (1, 2)));
    assert(h1.drop_last() =~= g);
    let s2 = apply(s1, dc());
    assert(run(h1) == s2);
    assert(s2[(1, 1)].succ == ISet::<Id>::empty().insert((2, 3)));
    assert(s2[(1, 2)].succ =~= ISet::<Id>::empty());
    assert(s2[(1, 2)].op.val == Some(20nat));
    assert(s2[(2, 3)].op.val.is_none());
    assert(visible_ids(s2, 7) =~= ISet::<Id>::empty().insert((1, 2)));
}

fn main() {}

} // verus!
