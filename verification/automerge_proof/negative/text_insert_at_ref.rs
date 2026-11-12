// Verus model of Automerge's text/list sequence layer (RGA) with INCREMENTAL insertion.
// See CRDT_NOTES.md. Self-contained (vstd only).
//
// Real mechanism being modelled (vendor/automerge-0.10.0/src/op_set2/change/batch.rs, `Untangler`):
//  - a new insert op is placed after its reference element; stack entries (pending new elements)
//    whose id is greater than the id of the next existing insert element are popped and placed
//    BEFORE that element (batch.rs:152-169 `untangle_inserts`:
//       `if let Err(n) = self.stack.binary_search_by(|n| self.change_ops[*n].id().cmp(&id)) {
//            while self.stack.len() > n { self.untangle_inner(insert_pos, log); } }`).
//    For one pending op that is the classic RGA scan: after the reference element, skip elements
//    with a greater id; insert before the first element with a smaller id (or at the end).
//    Non-insert ops (updates/deletes) never move elements (batch.rs:108-123 `element_update`).
//  - a delete is a succ entry on the element: op_set2/op_set.rs:245 `add_succ`; the element is
//    visible iff it has no succ (op_set.rs:650). A text splice = a run of inserts + deletes.
// The batch code is one-op-at-a-time here; the model is NOT a refinement of the columnar code (trusted).
use vstd::prelude::*;

verus! {

pub type Id = (nat, nat); // OpId = (counter, actor index)

pub open spec fn idlt(a: Id, b: Id) -> bool {
    a.0 < b.0 || (a.0 == b.0 && a.1 < b.1)
}

pub open spec fn gt(a: Id, b: Id) -> bool { idlt(b, a) }

pub proof fn lemma_idlt_trans(a: Id, b: Id, c: Id)
    requires idlt(a, b), idlt(b, c),
    ensures idlt(a, c),
{}

pub struct El {
    pub id: Id,
    pub rf: Option<Id>, // None = HEAD
    pub ch: nat,
}

pub type List = Seq<El>;

// ---- the invariant characterising an RGA list ----
// every element follows its reference element, and every element strictly between the reference
// and the element has a greater id than the element.  (HEAD = position -1.)
pub open spec fn ok_at(l: List, i: int) -> bool {
    match l[i].rf {
        None => forall|k: int| 0 <= k < i ==> gt(l[k].id, l[i].id),
        Some(r) => idlt(r, l[i].id)
            && exists|j: int| 0 <= j < i && l[j].id == r && (forall|k: int| j < k < i ==> gt(l[k].id, l[i].id)),
    }
}

pub open spec fn inv(l: List) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i].id != l[j].id
    &&& forall|i: int| 0 <= i < l.len() ==> ok_at(l, i)
}

pub open spec fn contains_id(l: List, id: Id) -> bool {
    exists|j: int| 0 <= j < l.len() && l[j].id == id
}

pub open spec fn idx(l: List, id: Id) -> int {
    choose|j: int| 0 <= j < l.len() && l[j].id == id
}

// ---- incremental insertion: the RGA scan ----
pub open spec fn scan(l: List, pos: int, id: Id) -> int
    decreases l.len() - pos,
{
    if 0 <= pos < l.len() && gt(l[pos].id, id) { scan(l, pos + 1, id) } else { pos }
}

pub open spec fn start(l: List, e: El) -> int {
    match e.rf { None => 0, Some(r) => idx(l, r) }
}

pub open spec fn slot(l: List, e: El) -> int { scan(l, start(l, e), e.id) }

pub open spec fn ins(l: List, e: El) -> List { l.insert(slot(l, e), e) }

// causal readiness of an insert
pub open spec fn ready(l: List, e: El) -> bool {
    &&& !contains_id(l, e.id)
    &&& match e.rf { None => true, Some(r) => contains_id(l, r) && idlt(r, e.id) }
}

proof fn lemma_scan(l: List, pos: int, id: Id)
    requires 0 <= pos <= l.len(), inv(l),
    ensures
        pos <= scan(l, pos, id) <= l.len(),
        forall|k: int| pos <= k < scan(l, pos, id) ==> gt(l[k].id, id),
        scan(l, pos, id) < l.len() ==> !gt(l[scan(l, pos, id)].id, id),
    decreases l.len() - pos,
{
    if pos < l.len() && gt(l[pos].id, id) {
        lemma_scan(l, pos + 1, id);
        assert forall|k: int| pos <= k < scan(l, pos, id) implies gt(l[k].id, id) by {
            if k > pos {} 
        }
    }
}

pub proof fn lemma_ins_preserves(l: List, e: El)
    requires inv(l), ready(l, e),
    ensures inv(ins(l, e)),
{
    let s = slot(l, e);
    let st = start(l, e);
    let l2 = ins(l, e);
    assert(st >= 0 && st <= l.len()) by {
        if let Some(r) = e.rf {
            let j = idx(l, r);
            assert(0 <= j < l.len());
        }
    }
    lemma_scan(l, st, e.id);
    assert(l2.len() == l.len() + 1);
    assert(l2[s] == e);
    assert forall|k: int| 0 <= k < s implies l2[k] == l[k] by {}
    assert forall|k: int| s < k < l2.len() implies l2[k] == l[k - 1] by {}
    // distinctness
    assert forall|i: int, j: int| 0 <= i < j < l2.len() implies l2[i].id != l2[j].id by {
        if i == s { assert(l2[j] == l[j - 1]); assert(l[j-1].id != e.id) by { assert(contains_id(l, l[j-1].id)); } }
        else if j == s { assert(l2[i] == l[i]); assert(l[i].id != e.id) by { assert(contains_id(l, l[i].id)); } }
    }
    assert forall|i: int| 0 <= i < l2.len() implies ok_at(l2, i) by {
        if i == s {
            match e.rf {
                None => {
                    assert(st == 0);
                    assert forall|k: int| 0 <= k < i implies gt(l2[k].id, l2[i].id) by { assert(l2[k] == l[k]); }
                }
                Some(r) => {
                    let j = idx(l, r);
                    assert(st == j + 1);
                    assert(l2[j] == l[j]);
                    assert(0 <= j < i);
                    assert forall|k: int| j < k < i implies gt(l2[k].id, l2[i].id) by { assert(l2[k] == l[k]); }
                }
            }
        } else if i < s {
            assert(l2[i] == l[i]);
            assert(ok_at(l, i));
            match l[i].rf {
                None => {
                    assert forall|k: int| 0 <= k < i implies gt(l2[k].id, l2[i].id) by { assert(l2[k] == l[k]); }
                }
                Some(r) => {
                    let j = choose|j: int| 0 <= j < i && l[j].id == r && (forall|k: int| j < k < i ==> gt(l[k].id, l[i].id));
                    assert(l2[j] == l[j]);
                    assert forall|k: int| j < k < i implies gt(l2[k].id, l2[i].id) by { assert(l2[k] == l[k]); }
                }
            }
        } else {
            let f = l[i - 1];
            assert(l2[i] == f);
            assert(ok_at(l, i - 1));
            // e's id beats f's id when e lands between f's reference and f
            match f.rf {
                None => {
                    assert forall|k: int| 0 <= k < i implies gt(l2[k].id, l2[i].id) by {
                        if k < s { assert(l2[k] == l[k]); }
                        else if k == s {
                            assert(l2[k] == e);
                            if s == i - 1 { assert(l[s].id == f.id); }
                            else { assert(gt(l[s].id, f.id)); }
                            assert(idlt(l[s].id, e.id)); 
                        }
                        else { assert(l2[k] == l[k - 1]); }
                    }
                }
                Some(r) => {
                    let j = choose|j: int| 0 <= j < i - 1 && l[j].id == r && (forall|k: int| j < k < i - 1 ==> gt(l[k].id, f.id));
                    let j2 = if j < s { j } else { j + 1 };
                    assert(l2[j2] == l[j]);
                    assert(0 <= j2 < i);
                    assert forall|k: int| j2 < k < i implies gt(l2[k].id, l2[i].id) by {
                        if k < s { assert(l2[k] == l[k]); }
                        else if k == s {
                            assert(l2[k] == e);
                            assert(j < s);
                            if s == i - 1 { assert(l[s].id == f.id); }
                            else { assert(gt(l[s].id, f.id)); }
                            assert(idlt(l[s].id, e.id));
                        }
                        else { assert(l2[k] == l[k - 1]); }
                    }
                }
            }
        }
    }
}

// ---- uniqueness: two lists satisfying inv over the same elements are equal ----
pub open spec fn els(l: List) -> ISet<El> { ISet::new(|e: El| l.contains(e)) }

// m has the greatest id of a non-empty list
pub open spec fn is_max(l: List, k: int) -> bool {
    0 <= k < l.len() && forall|i: int| 0 <= i < l.len() && i != k ==> gt(l[k].id, l[i].id)
}

proof fn lemma_has_max(l: List)
    requires l.len() > 0, inv(l),
    ensures exists|k: int| is_max(l, k),
    decreases l.len(),
{
    if l.len() == 1 {
        assert(is_max(l, 0));
    } else {
        let t = l.drop_last();
        assert(inv(t)) by {
            assert forall|i: int| 0 <= i < t.len() implies ok_at(t, i) by {
                assert(t[i] == l[i]);
                assert(ok_at(l, i));
                match t[i].rf {
                    None => { assert forall|k: int| 0 <= k < i implies gt(t[k].id, t[i].id) by { assert(t[k] == l[k]); } }
                    Some(r) => {
                        let j = choose|j: int| 0 <= j < i && l[j].id == r && (forall|k: int| j < k < i ==> gt(l[k].id, l[i].id));
                        assert(t[j] == l[j]);
                        assert forall|k: int| j < k < i implies gt(t[k].id, t[i].id) by { assert(t[k] == l[k]); }
                    }
                }
            }
        }
        lemma_has_max(t);
        let k = choose|k: int| is_max(t, k);
        let n = l.len() - 1;
        assert(l[n].id != l[k].id);
        if gt(l[k].id, l[n].id) {
            assert(is_max(l, k)) by {
                assert forall|i: int| 0 <= i < l.len() && i != k implies gt(l[k].id, l[i].id) by {
                    if i < n { assert(t[i] == l[i]); }
                }
            }
        } else {
            assert(is_max(l, n)) by {
                assert forall|i: int| 0 <= i < l.len() && i != n implies gt(l[n].id, l[i].id) by {
                    assert(t[i] == l[i]);
                    if i != k { assert(gt(l[k].id, l[i].id)); } 
                }
            }
        }
    }
}

// removing the max element keeps inv, its reference is directly before it, and nothing refers to it
proof fn lemma_remove_max(l: List, k: int)
    requires inv(l), is_max(l, k),
    ensures
        inv(l.remove(k)),
        match l[k].rf {
            None => k == 0,
            Some(r) => k >= 1 && l[k - 1].id == r,
        },
        forall|i: int| 0 <= i < l.len() ==> l[i].rf != Some(l[k].id),
{
    let m = l[k];
    let t = l.remove(k);
    assert(t.len() == l.len() - 1);
    assert forall|i: int| 0 <= i < t.len() implies t[i] == (if i < k { l[i] } else { l[i + 1] }) by {}
    // nothing refers to m: a referrer has a greater id (Lamport) but m is max
    assert forall|i: int| 0 <= i < l.len() implies l[i].rf != Some(m.id) by {
        assert(ok_at(l, i));
        if l[i].rf == Some(m.id) {
            assert(idlt(m.id, l[i].id));
            if i != k { assert(gt(m.id, l[i].id)); }
            else { assert(ok_at(l, k)); }
        }
    }
    // reference immediately before
    assert(ok_at(l, k));
    match m.rf {
        None => {
            if k > 0 { assert(gt(l[0].id, m.id)); assert(gt(m.id, l[0].id)); }
        }
        Some(r) => {
            let j = choose|j: int| 0 <= j < k && l[j].id == r && (forall|q: int| j < q < k ==> gt(l[q].id, m.id));
            if j < k - 1 { assert(gt(l[k - 1].id, m.id)); assert(gt(m.id, l[k - 1].id)); }
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < t.len() implies t[i].id != t[j].id by {}
    assert forall|i: int| 0 <= i < t.len() implies ok_at(t, i) by {
        let oi = if i < k { i } else { i + 1 };
        assert(t[i] == l[oi]);
        assert(ok_at(l, oi));
        match t[i].rf {
            None => {
                assert forall|q: int| 0 <= q < i implies gt(t[q].id, t[i].id) by {
                    let oq = if q < k { q } else { q + 1 };
                    assert(t[q] == l[oq]);
                    assert(oq < oi);
                }
            }
            Some(r) => {
                let j = choose|j: int| 0 <= j < oi && l[j].id == r && (forall|q: int| j < q < oi ==> gt(l[q].id, l[oi].id));
                assert(j != k) by { if j == k { assert(l[i].rf == Some(m.id)); } }
                let tj = if j < k { j } else { j - 1 };
                assert(t[tj] == l[j]);
                assert(0 <= tj < i);
                assert forall|q: int| tj < q < i implies gt(t[q].id, t[i].id) by {
                    let oq = if q < k { q } else { q + 1 };
                    assert(t[q] == l[oq]);
                    assert(j < oq < oi);
                }
            }
        }
    }
}

pub proof fn lemma_unique(a: List, b: List)
    requires inv(a), inv(b), els(a) == els(b), forall|x: El, y: El| els(a).contains(x) && els(a).contains(y) && x.id == y.id ==> x == y,
    ensures a == b,
    decreases a.len(),
{
    // same length: distinct ids and same element sets
    if a.len() == 0 {
        assert(b.len() == 0) by { if b.len() > 0 { assert(els(b).contains(b[0])); assert(els(a).contains(b[0])); assert(a.contains(b[0])); } }
        assert(a =~= b);
    } else {
        lemma_has_max(a);
        let ka = choose|k: int| is_max(a, k);
        let m = a[ka];
        assert(els(a).contains(m));
        assert(b.contains(m));
        let kb = choose|k: int| 0 <= k < b.len() && b[k] == m;
        // m is also max in b: b's max element has the id of the max of els
        lemma_has_max(b);
        let kb2 = choose|k: int| is_max(b, k);
        let mb = b[kb2];
        assert(els(a).contains(mb)); assert(a.contains(mb));
        let ia = choose|i: int| 0 <= i < a.len() && a[i] == mb;
        if ia != ka { assert(gt(m.id, mb.id)); }
        if kb != kb2 { assert(gt(mb.id, m.id)); }
        assert(mb.id == m.id) by {
            if ia == ka { } else { assert(kb != kb2 || true); assert(false); }
        }
        assert(mb == m) by { assert(els(a).contains(mb) && els(a).contains(m)); }
        assert(kb2 == kb) by { if kb != kb2 { assert(b[kb].id != b[kb2].id); } }
        lemma_remove_max(a, ka);
        lemma_remove_max(b, kb);
        let ta = a.remove(ka);
        let tb = b.remove(kb);
        assert(els(ta) =~= els(a).remove(m)) by {
            assert forall|x: El| els(ta).contains(x) == els(a).remove(m).contains(x) by {
                if ta.contains(x) {
                    let i = choose|i: int| 0 <= i < ta.len() && ta[i] == x;
                    let oi = if i < ka { i } else { i + 1 };
                    assert(a[oi] == x); assert(a.contains(x));
                    assert(x != m) by { if x == m { assert(a[oi].id == a[ka].id); } }
                }
                if els(a).remove(m).contains(x) {
                    let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
                    assert(i != ka);
                    let ti = if i < ka { i } else { i - 1 };
                    assert(ta[ti] == x);
                }
            }
        }
        assert(els(tb) =~= els(b).remove(m)) by {
            assert forall|x: El| els(tb).contains(x) == els(b).remove(m).contains(x) by {
                if tb.contains(x) {
                    let i = choose|i: int| 0 <= i < tb.len() && tb[i] == x;
                    let oi = if i < kb { i } else { i + 1 };
                    assert(b[oi] == x); assert(b.contains(x));
                    assert(x != m) by { if x == m { assert(b[oi].id == b[kb].id); } }
                }
                if els(b).remove(m).contains(x) {
                    let i = choose|i: int| 0 <= i < b.len() && b[i] == x;
                    assert(i != kb);
                    let ti = if i < kb { i } else { i - 1 };
                    assert(tb[ti] == x);
                }
            }
        }
        assert(els(ta) == els(tb));
        assert forall|x: El, y: El| els(ta).contains(x) && els(ta).contains(y) && x.id == y.id implies x == y by {
            assert(els(a).contains(x) && els(a).contains(y));
        }
        lemma_unique(ta, tb);
        // reinsert m at the same place: its reference is directly before it in both
        assert(a =~= b) by {
            assert(a.len() == b.len()) by { assert(ta.len() == tb.len()); }
            assert(ta == tb);
            assert(ka == kb) by {
                match m.rf {
                    None => {}
                    Some(r) => {
                        assert(a[ka - 1].id == r && b[kb - 1].id == r);
                        assert(ta[ka - 1] == a[ka - 1]);
                        assert(tb[kb - 1] == b[kb - 1]);
                        // r occurs once in ta == tb
                        assert(ta[ka - 1].id == tb[kb - 1].id);
                        if ka != kb {
                            assert(ta[ka-1].id != ta[kb-1].id) by { assert(inv(ta)); }
                        }
                    }
                }
            }
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                if i < ka { assert(a[i] == ta[i]); assert(b[i] == tb[i]); }
                else if i > ka { assert(a[i] == ta[i - 1]); assert(b[i] == tb[i - 1]); }
            }
        }
    }
}

// ===================== delivery histories: strong eventual consistency =====================
pub enum TOp {
    Ins(El),
    Del { id: Id, target: Id }, // delete op: adds `id` to the succ of the element `target`
}

pub struct TState {
    pub list: List,
    pub dels: ISet<Id>, // targets that have a succ (deleted)
    pub seen: ISet<Id>, // ids of all applied ops
}

pub open spec fn tinit() -> TState {
    TState { list: Seq::empty(), dels: ISet::empty(), seen: ISet::empty() }
}

pub open spec fn tready(s: TState, o: TOp) -> bool {
    match o {
        TOp::Ins(e) => !s.seen.contains(e.id) && ready(s.list, e),
        TOp::Del { id, target } => !s.seen.contains(id) && contains_id(s.list, target) && idlt(target, id),
    }
}

pub open spec fn tapply(s: TState, o: TOp) -> TState {
    match o {
        TOp::Ins(e) => TState { list: ins(s.list, e), dels: s.dels, seen: s.seen.insert(e.id) },
        TOp::Del { id, target } => TState { list: s.list, dels: s.dels.insert(target), seen: s.seen.insert(id) },
    }
}

// causally valid history: every op is causally ready when applied (what Automerge's queue ensures)
pub open spec fn tvalid(h: Seq<TOp>) -> bool
    decreases h.len(),
{
    if h.len() == 0 { true } else { tvalid(h.drop_last()) && tready(trun(h.drop_last()), h.last()) }
}

pub open spec fn trun(h: Seq<TOp>) -> TState
    decreases h.len(),
{
    if h.len() == 0 { tinit() } else { tapply(trun(h.drop_last()), h.last()) }
}

pub open spec fn ops_of(h: Seq<TOp>) -> ISet<TOp> { ISet::new(|o: TOp| h.contains(o)) }

pub open spec fn inserted(h: Seq<TOp>) -> ISet<El> { ISet::new(|e: El| h.contains(TOp::Ins(e))) }

pub open spec fn deleted(h: Seq<TOp>) -> ISet<Id> {
    ISet::new(|t: Id| exists|i: Id| h.contains(TOp::Del { id: i, target: t }))
}

pub open spec fn visible_text(s: TState) -> Seq<nat> {
    s.list.filter(|e: El| !s.dels.contains(e.id)).map_values(|e: El| e.ch)
}

proof fn lemma_els_ins(l: List, e: El)
    requires inv(l), ready(l, e),
    ensures els(ins(l, e)) == els(l).insert(e),
{
    let l2 = ins(l, e);
    let s = slot(l, e);
    let st = start(l, e);
    assert(0 <= st <= l.len()) by { if let Some(r) = e.rf { let j = idx(l, r); assert(0 <= j < l.len()); } }
    lemma_scan(l, st, e.id);
    assert forall|x: El| els(l2).contains(x) == els(l).insert(e).contains(x) by {
        if l2.contains(x) {
            let i = choose|i: int| 0 <= i < l2.len() && l2[i] == x;
            if i < s { assert(l[i] == x); }
            else if i > s { assert(l[i - 1] == x); }
        }
        if l.contains(x) {
            let i = choose|i: int| 0 <= i < l.len() && l[i] == x;
            if i < s { assert(l2[i] == x); } else { assert(l2[i + 1] == x); }
        }
        if x == e { assert(l2[s] == e); }
    }
    assert(els(l2) =~= els(l).insert(e));
}

pub proof fn lemma_run_facts(h: Seq<TOp>)
    requires tvalid(h),
    ensures
        inv(trun(h).list),
        els(trun(h).list) == inserted(h),
        trun(h).dels == deleted(h),
    decreases h.len(),
{
    if h.len() == 0 {
        assert(els(Seq::<El>::empty()) =~= inserted(h));
        assert(deleted(h) =~= ISet::<Id>::empty());
        assert(inv(Seq::<El>::empty()));
    } else {
        let g = h.drop_last();
        lemma_run_facts(g);
        let s = trun(g);
        let o = h.last();
        assert(tready(s, o));
        assert forall|x: TOp| h.contains(x) == (g.contains(x) || x == o) by {
            if h.contains(x) { let i = choose|i: int| 0 <= i < h.len() && h[i] == x; if i < g.len() { assert(g[i] == x); } }
            if g.contains(x) { let i = choose|i: int| 0 <= i < g.len() && g[i] == x; assert(h[i] == x); }
            if x == o { assert(h[h.len() - 1] == o); }
        }
        match o {
            TOp::Ins(e) => {
                lemma_ins_preserves(s.list, e);
                lemma_els_ins(s.list, e);
                assert(inserted(h) =~= inserted(g).insert(e));
                assert(deleted(h) =~= deleted(g));
            }
            TOp::Del { id, target } => {
                assert(inserted(h) =~= inserted(g));
                assert(deleted(h) =~= deleted(g).insert(target)) by {
                    assert forall|t: Id| deleted(h).contains(t) == deleted(g).insert(target).contains(t) by {
                        if t == target { assert(h.contains(TOp::Del { id: id, target: target })); }
                        if deleted(h).contains(t) {
                            let i = choose|i: Id| h.contains(TOp::Del { id: i, target: t });
                            if t != target { assert(g.contains(TOp::Del { id: i, target: t })); }
                        }
                        if deleted(g).contains(t) {
                            let i = choose|i: Id| g.contains(TOp::Del { id: i, target: t });
                            assert(h.contains(TOp::Del { id: i, target: t }));
                        }
                    }
                }
            }
        }
    }
}

// THEOREM (strong eventual consistency of text): two causally valid delivery orders of the same set
// of ops give the same list (hence the same visible text) and the same deletions.
pub proof fn theorem_sec_text(h1: Seq<TOp>, h2: Seq<TOp>)
    requires tvalid(h1), tvalid(h2), ops_of(h1) =~= ops_of(h2),
    ensures
        trun(h1).list == trun(h2).list,
        trun(h1).dels == trun(h2).dels,
        visible_text(trun(h1)) == visible_text(trun(h2)),
{
    lemma_run_facts(h1);
    lemma_run_facts(h2);
    assert(inserted(h1) =~= inserted(h2)) by {
        assert forall|e: El| inserted(h1).contains(e) == inserted(h2).contains(e) by {
            assert(ops_of(h1).contains(TOp::Ins(e)) == ops_of(h2).contains(TOp::Ins(e)));
        }
    }
    assert(deleted(h1) =~= deleted(h2)) by {
        assert forall|t: Id| deleted(h1).contains(t) == deleted(h2).contains(t) by {
            if deleted(h1).contains(t) {
                let i = choose|i: Id| h1.contains(TOp::Del { id: i, target: t });
                assert(ops_of(h1).contains(TOp::Del { id: i, target: t }));
                assert(h2.contains(TOp::Del { id: i, target: t }));
            }
            if deleted(h2).contains(t) {
                let i = choose|i: Id| h2.contains(TOp::Del { id: i, target: t });
                assert(ops_of(h2).contains(TOp::Del { id: i, target: t }));
                assert(h1.contains(TOp::Del { id: i, target: t }));
            }
        }
    }
    let a = trun(h1).list;
    let b = trun(h2).list;
    assert forall|x: El, y: El| els(a).contains(x) && els(a).contains(y) && x.id == y.id implies x == y by {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
        let j = choose|j: int| 0 <= j < a.len() && a[j] == y;
        if i != j { if i < j { assert(a[i].id != a[j].id); } else { assert(a[j].id != a[i].id); } }
    }
    lemma_unique(a, b);
}

// ---- reachability: concurrent inserts at one reference (with a scan that skips), and a delete ----
pub open spec fn ex() -> El { El { id: (1, 1), rf: None, ch: 120 } }          // 'x' after HEAD
pub open spec fn ey() -> El { El { id: (2, 1), rf: Some((1, 1)), ch: 121 } }  // 'y' after x, actor 1
pub open spec fn ez() -> El { El { id: (3, 2), rf: Some((1, 1)), ch: 122 } }  // 'z' after x, actor 2 (concurrent with y, higher id)
pub open spec fn edl() -> TOp { TOp::Del { id: (4, 1), target: (1, 1) } }     // delete x

pub proof fn example_run()
    ensures
        tvalid(seq![TOp::Ins(ex()), TOp::Ins(ey()), TOp::Ins(ez())]),
        tvalid(seq![TOp::Ins(ex()), TOp::Ins(ez()), TOp::Ins(ey())]),
        trun(seq![TOp::Ins(ex()), TOp::Ins(ey()), TOp::Ins(ez())]).list == seq![ex(), ez(), ey()],
        trun(seq![TOp::Ins(ex()), TOp::Ins(ez()), TOp::Ins(ey())]).list == seq![ex(), ez(), ey()],
        // with the delete of x: visible text is "zy" (z=122, y=121)
        tvalid(seq![TOp::Ins(ex()), TOp::Ins(ez()), TOp::Ins(ey()), edl()]),
        visible_text(trun(seq![TOp::Ins(ex()), TOp::Ins(ez()), TOp::Ins(ey()), edl()])) == seq![122nat, 121nat],
{
    let h0 = Seq::<TOp>::empty();
    let h1 = seq![TOp::Ins(ex())];
    let ha = seq![TOp::Ins(ex()), TOp::Ins(ey())];
    let haa = seq![TOp::Ins(ex()), TOp::Ins(ey()), TOp::Ins(ez())];
    let hb = seq![TOp::Ins(ex()), TOp::Ins(ez())];
    let hbb = seq![TOp::Ins(ex()), TOp::Ins(ez()), TOp::Ins(ey())];
    let hbd = seq![TOp::Ins(ex()), TOp::Ins(ez()), TOp::Ins(ey()), edl()];
    assert(h1.drop_last() =~= h0);
    assert(ha.drop_last() =~= h1);
    assert(haa.drop_last() =~= ha);
    assert(hb.drop_last() =~= h1);
    assert(hbb.drop_last() =~= hb);
    assert(hbd.drop_last() =~= hbb);
    let s1 = tapply(tinit(), TOp::Ins(ex()));
    assert(trun(h0) == tinit());
    assert(h1.last() == TOp::Ins(ex()));
    assert(trun(h1) == s1);
    assert(s1.list =~= seq![ex()]);
    // scan evaluations
    assert(slot(s1.list, ey()) == 1) by { reveal_with_fuel(scan, 3); }
    assert(slot(s1.list, ez()) == 1) by { reveal_with_fuel(scan, 3); }
    let sa = tapply(s1, TOp::Ins(ey()));
    assert(trun(ha) == sa);
    assert(sa.list =~= seq![ex(), ey()]);
    // z after y: skip? y.id=(2,1) > z.id? no: z=(3,2) is greater, so z goes before y
    assert(slot(sa.list, ez()) == 1) by { reveal_with_fuel(scan, 3); }
    let sb = tapply(s1, TOp::Ins(ez()));
    assert(trun(hb) == sb);
    assert(sb.list =~= seq![ex(), ez()]);
    // y after z: scan skips z? gt(z.id, y.id) holds, so skip -> slot 2
    assert(slot(sb.list, ey()) == 2) by { reveal_with_fuel(scan, 4); }
    assert(trun(haa).list =~= seq![ex(), ez(), ey()]);
    assert(trun(hbb).list =~= seq![ex(), ez(), ey()]);
    assert(tvalid(h0));
    assert(tvalid(h1)) by { assert(tready(trun(h0), TOp::Ins(ex()))) by { assert(!contains_id(Seq::<El>::empty(), ex().id)); } }
    assert(tvalid(ha)) by { assert(contains_id(s1.list, (1, 1))) by { assert(s1.list[0].id == (1, 1)); } assert(!contains_id(s1.list, ey().id)) by { assert(forall|j: int| 0 <= j < s1.list.len() ==> s1.list[j].id != ey().id); } }
    assert(tvalid(haa)) by { assert(contains_id(sa.list, (1, 1))) by { assert(sa.list[0].id == (1, 1)); } assert(!contains_id(sa.list, ez().id)) by { assert(forall|j: int| 0 <= j < sa.list.len() ==> sa.list[j].id != ez().id); } }
    assert(tvalid(hb)) by { assert(contains_id(s1.list, (1, 1))) by { assert(s1.list[0].id == (1, 1)); } assert(!contains_id(s1.list, ez().id)) by { assert(forall|j: int| 0 <= j < s1.list.len() ==> s1.list[j].id != ez().id); } }
    assert(tvalid(hbb)) by { assert(contains_id(sb.list, (1, 1))) by { assert(sb.list[0].id == (1, 1)); } assert(!contains_id(sb.list, ey().id)) by { assert(forall|j: int| 0 <= j < sb.list.len() ==> sb.list[j].id != ey().id); } }
    let sc = trun(hbb);
    assert(tvalid(hbd)) by {
        assert(contains_id(sc.list, (1, 1))) by { assert(sc.list[0].id == (1, 1)); }
        assert(!sc.seen.contains((4, 1)));
    }
    let sd = trun(hbd);
    assert(sd.list =~= seq![ex(), ez(), ey()]);
    assert(sd.dels == sc.dels.insert((1, 1)));
    assert(visible_text(sd) =~= seq![122nat, 121nat]) by {
        let f = sd.list.filter(|e: El| !sd.dels.contains(e.id));
        assert(sd.dels.contains((1, 1)));
        assert(!sd.dels.contains((1, 2)) || true);
        reveal_with_fuel(Seq::filter, 4);
    }
}

fn main() {}

} // verus!
