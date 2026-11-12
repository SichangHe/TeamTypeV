// NEGATIVE CONTROL: pops the entries with SMALLER id than the doc element (keeps greater ones) instead of the greater ones (must be rejected)
// Verus model of Automerge's SINGLE-PASS BATCH insertion into a list (batch.rs `Untangler`/`walk_list`)
// and a proof that it equals sequential one-op RGA insertion (crdt_text.rs `ins`). See CRDT_NOTES.md.
// Self-contained (vstd only). Everything before the line "NEW" is copied from crdt_text.rs
// (RGA defs, lemma_ins_preserves, lemma_unique, lemma_els_ins).
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
    match e.rf { None => 0, Some(r) => idx(l, r) + 1 }
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

// ===================== NEW: batch insertion =====================

// Batch ops are El with `rf`. kids(ops, r) = the ops whose reference is r, in the order of `ops`
// (batch.rs Untangler::new: `entry`/`gosub`/`stack` all hold exactly these lists, in change_ops order).
pub open spec fn kids(ops: Seq<El>, r: Option<Id>) -> Seq<El>
    decreases ops.len(),
{
    if ops.len() == 0 { Seq::empty() } else {
        let k = kids(ops.drop_last(), r);
        if ops.last().rf == r { k.push(ops.last()) } else { k }
    }
}

// number of ops not yet in out (termination measure only)
pub open spec fn cnt(ops: Seq<El>, out: List) -> nat
    decreases ops.len(),
{
    if ops.len() == 0 { 0 } else {
        cnt(ops.drop_last(), out) + (if out.contains(ops.last()) { 0nat } else { 1nat })
    }
}

// `while self.stack.len() > n { self.untangle_inner(..) }` : pop the top op, place it in `out`,
// then push its gosub children (= kids of its id).  The extra guard (top is a batch op not yet placed)
// is only for termination; the proof shows it always holds.
pub proof fn lemma_cnt_dec(ops: Seq<El>, out: List, x: El)
    requires ops.contains(x), !out.contains(x),
    ensures cnt(ops, out.push(x)) < cnt(ops, out),
    decreases ops.len(),
{
    let t = ops.drop_last();
    let o2 = out.push(x);
    assert(forall|y: El| out.contains(y) ==> o2.contains(y)) by {
        assert forall|y: El| out.contains(y) implies o2.contains(y) by {
            let k = choose|k: int| 0 <= k < out.len() && out[k] == y;
            assert(o2[k] == y);
        }
    }
    lemma_cnt_mono(t, out, x);
    if ops.last() == x {
        assert(o2.contains(x)) by { assert(o2[out.len() as int] == x); }
    } else {
        assert(t.contains(x)) by {
            let k = choose|k: int| 0 <= k < ops.len() && ops[k] == x;
            assert(k < t.len());
            assert(t[k] == x);
        }
        lemma_cnt_dec(t, out, x);
        if out.contains(ops.last()) { assert(o2.contains(ops.last())); }
    }
}

pub proof fn lemma_cnt_mono(ops: Seq<El>, out: List, x: El)
    ensures cnt(ops, out.push(x)) <= cnt(ops, out),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let t = ops.drop_last();
        lemma_cnt_mono(t, out, x);
        let o2 = out.push(x);
        if out.contains(ops.last()) {
            let k = choose|k: int| 0 <= k < out.len() && out[k] == ops.last();
            assert(o2[k] == ops.last());
        }
    }
}

#[verifier::decreases_by]
proof fn drain_dec(ops: Seq<El>, stack: Seq<El>, n: nat, out: List) {
    if stack.len() > n && ops.contains(stack.last()) && !out.contains(stack.last()) {
        lemma_cnt_dec(ops, out, stack.last());
    }
}

pub open spec fn drain(ops: Seq<El>, stack: Seq<El>, n: nat, out: List) -> (Seq<El>, List)
    decreases cnt(ops, out),
    via drain_dec
{
    if stack.len() > n && ops.contains(stack.last()) && !out.contains(stack.last()) {
        let x = stack.last();
        drain(ops, stack.drop_last().add(kids(ops, Some(x.id))), n, out.push(x))
    } else {
        (stack, out)
    }
}

// n = what `stack.binary_search_by(id.cmp(&id))` returns as Err(n) on an ascending stack:
// the number of entries with smaller id (index after the last smaller entry).
pub open spec fn pp(s: Seq<El>, id: Id) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else if idlt(id, s.last().id) { s.len() } else { pp(s.drop_last(), id) }
}

// walk_list: for each doc element d: untangle_inserts(d.id) = pop down to n, then push entry[d.id];
// then d is emitted.  At the end finish_inserts drains the stack (n = 0).
pub open spec fn walk(list: List, ops: Seq<El>, i: nat, out: List, stack: Seq<El>) -> List
    decreases list.len() - i,
{
    if i >= list.len() {
        drain(ops, stack, 0, out).1
    } else {
        let d = list[i as int];
        let r = drain(ops, stack, pp(stack, d.id), out);
        walk(list, ops, i + 1, r.1.push(d), r.0.add(kids(ops, Some(d.id))))
    }
}

// Untangler::new: stack = ops referencing HEAD
pub open spec fn batch_ins(list: List, ops: Seq<El>) -> List {
    walk(list, ops, 0, Seq::empty(), kids(ops, None))
}

// ---- validity assumptions ----
pub open spec fn sorted_ops(ops: Seq<El>) -> bool {
    forall|a: int, b: int| 0 <= a < b < ops.len() ==> idlt(ops[a].id, ops[b].id)
}

pub open spec fn valid_ops(list: List, ops: Seq<El>) -> bool {
    &&& inv(list)
    &&& sorted_ops(ops)
    &&& forall|k: int| 0 <= k < ops.len() ==> !contains_id(list, ops[k].id)
    &&& forall|k: int| 0 <= k < ops.len() ==> valid_ref(list, ops, #[trigger] ops[k])
}

pub open spec fn valid_ref(list: List, ops: Seq<El>, e: El) -> bool {
    match e.rf {
        None => true,
        Some(r) => idlt(r, e.id) && (contains_id(list, r) || contains_id(ops, r)),
    }
}


// ============================ proofs ============================
pub open spec fn lam(ops: Seq<El>) -> bool {
    forall|k: int| 0 <= k < ops.len() ==> match (#[trigger] ops[k]).rf { None => true, Some(r) => idlt(r, ops[k].id) }
}

pub open spec fn asc(s: Seq<El>) -> bool {
    forall|a: int, b: int| 0 <= a < b < s.len() ==> idlt(s[a].id, s[b].id)
}

pub proof fn lemma_kids(ops: Seq<El>, r: Option<Id>)
    ensures
        forall|k: int| 0 <= k < kids(ops, r).len() ==> ops.contains(#[trigger] kids(ops, r)[k]) && kids(ops, r)[k].rf == r,
        forall|e: El| ops.contains(e) && e.rf == r ==> kids(ops, r).contains(e),
        sorted_ops(ops) ==> asc(kids(ops, r)),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let t = ops.drop_last();
        lemma_kids(t, r);
        let k = kids(t, r);
        let l = ops.last();
        assert forall|j: int| 0 <= j < t.len() implies t[j] == ops[j] by {}
        assert forall|e: El| t.contains(e) implies ops.contains(e) by {
            let j = choose|j: int| 0 <= j < t.len() && t[j] == e;
            assert(ops[j] == e);
        }
        assert(ops.contains(l)) by { assert(ops[ops.len() - 1] == l); }
        if l.rf == r {
            let kk = k.push(l);
            assert forall|j: int| 0 <= j < kk.len() implies ops.contains(#[trigger] kk[j]) && kk[j].rf == r by {
                if j < k.len() { assert(kk[j] == k[j]); }
            }
            assert forall|e: El| ops.contains(e) && e.rf == r implies kk.contains(e) by {
                let j = choose|j: int| 0 <= j < ops.len() && ops[j] == e;
                if j < t.len() { assert(t[j] == e); assert(t.contains(e)); let q = choose|q: int| 0 <= q < k.len() && k[q] == e; assert(kk[q] == e); }
                else { assert(kk[k.len() as int] == l); assert(e == l); }
            }
            if sorted_ops(ops) {
                assert(sorted_ops(t));
                assert forall|a: int, b: int| 0 <= a < b < kk.len() implies idlt(kk[a].id, kk[b].id) by {
                    if b < k.len() { assert(kk[a] == k[a]); assert(kk[b] == k[b]); }
                    else {
                        assert(kk[b] == l);
                        assert(kk[a] == k[a]);
                        assert(t.contains(k[a]));
                        let q = choose|q: int| 0 <= q < t.len() && t[q] == k[a];
                        assert(idlt(ops[q].id, ops[ops.len() - 1].id));
                    }
                }
            }
        } else {
            assert forall|e: El| ops.contains(e) && e.rf == r implies k.contains(e) by {
                let j = choose|j: int| 0 <= j < ops.len() && ops[j] == e;
                if j < t.len() { assert(t[j] == e); assert(t.contains(e)); } else { assert(ops[ops.len() - 1] == l); assert(e == l); }
            }
            if sorted_ops(ops) { assert(sorted_ops(t)); }
        }
    }
}

// ---- stack invariant ----
pub open spec fn cond(out: List, x: El) -> bool {
    match x.rf {
        None => forall|k: int| 0 <= k < out.len() ==> gt(out[k].id, x.id),
        Some(r) => exists|j: int| 0 <= j < out.len() && out[j].id == r
            && (forall|k: int| j < k < out.len() ==> gt(out[k].id, x.id)),
    }
}

pub open spec fn stack_inv(ops: Seq<El>, out: List, stack: Seq<El>) -> bool {
    &&& asc(stack)
    &&& forall|k: int| 0 <= k < stack.len() ==>
        ops.contains(#[trigger] stack[k]) && !contains_id(out, stack[k].id) && cond(out, stack[k])
}

// completeness bookkeeping: every op is placed, on the stack, or still waiting for its reference
pub open spec fn jinv(ops: Seq<El>, out: List, stack: Seq<El>) -> bool {
    forall|k: int| 0 <= k < ops.len() ==> {
        let x = #[trigger] ops[k];
        out.contains(x) || stack.contains(x) || (match x.rf { None => false, Some(r) => !contains_id(out, r) })
    }
}

// appending an op whose `cond` holds keeps the RGA invariant
pub proof fn lemma_push_inv(out: List, x: El)
    requires inv(out), cond(out, x), !contains_id(out, x.id), match x.rf { None => true, Some(r) => idlt(r, x.id) },
    ensures inv(out.push(x)),
{
    let o2 = out.push(x);
    let n = out.len() as int;
    assert(o2[n] == x);
    assert forall|i: int, j: int| 0 <= i < j < o2.len() implies o2[i].id != o2[j].id by {
        if j == n { assert(o2[i] == out[i]); assert(contains_id(out, out[i].id)); }
        else { assert(o2[i] == out[i]); assert(o2[j] == out[j]); }
    }
    assert forall|i: int| 0 <= i < o2.len() implies ok_at(o2, i) by {
        if i < n {
            assert(o2[i] == out[i]);
            assert(ok_at(out, i));
            match out[i].rf {
                None => { assert forall|k: int| 0 <= k < i implies gt(o2[k].id, o2[i].id) by { assert(o2[k] == out[k]); } }
                Some(r) => {
                    let j = choose|j: int| 0 <= j < i && out[j].id == r && (forall|k: int| j < k < i ==> gt(out[k].id, out[i].id));
                    assert(o2[j] == out[j]);
                    assert forall|k: int| j < k < i implies gt(o2[k].id, o2[i].id) by { assert(o2[k] == out[k]); }
                }
            }
        } else {
            match x.rf {
                None => { assert forall|k: int| 0 <= k < i implies gt(o2[k].id, o2[i].id) by { assert(o2[k] == out[k]); } }
                Some(r) => {
                    let j = choose|j: int| 0 <= j < out.len() && out[j].id == r && (forall|k: int| j < k < out.len() ==> gt(out[k].id, x.id));
                    assert(o2[j] == out[j]);
                    assert forall|k: int| j < k < i implies gt(o2[k].id, o2[i].id) by { assert(o2[k] == out[k]); }
                }
            }
        }
    }
}

// inv implies: an element present in out has its reference present in out
pub proof fn lemma_ref_present(out: List, p: int)
    requires inv(out), 0 <= p < out.len(),
    ensures match out[p].rf { None => true, Some(r) => contains_id(out, r) },
{
    assert(ok_at(out, p));
    if let Some(r) = out[p].rf {
        let j = choose|j: int| 0 <= j < p && out[j].id == r && (forall|k: int| j < k < p ==> gt(out[k].id, out[p].id));
        assert(out[j].id == r);
    }
}

// pushing e to out keeps the stack invariant if e beats every stack entry
pub proof fn lemma_stack_push_out(ops: Seq<El>, out: List, stack: Seq<El>, e: El)
    requires stack_inv(ops, out, stack), forall|k: int| 0 <= k < stack.len() ==> gt(e.id, #[trigger] stack[k].id),
    ensures stack_inv(ops, out.push(e), stack),
{
    let o2 = out.push(e);
    let n = out.len() as int;
    assert(o2[n] == e);
    assert forall|k: int| 0 <= k < stack.len() implies
        ops.contains(#[trigger] stack[k]) && !contains_id(o2, stack[k].id) && cond(o2, stack[k]) by {
        let x = stack[k];
        assert(cond(out, x));
        assert(gt(e.id, x.id));
        assert(!contains_id(o2, x.id)) by {
            if contains_id(o2, x.id) {
                let q = choose|q: int| 0 <= q < o2.len() && o2[q].id == x.id;
                if q < n { assert(o2[q] == out[q]); assert(contains_id(out, x.id)); } else { assert(o2[q] == e); }
            }
        }
        match x.rf {
            None => { assert forall|q: int| 0 <= q < o2.len() implies gt(o2[q].id, x.id) by { if q < n { assert(o2[q] == out[q]); } } }
            Some(r) => {
                let j = choose|j: int| 0 <= j < out.len() && out[j].id == r && (forall|q: int| j < q < out.len() ==> gt(out[q].id, x.id));
                assert(o2[j] == out[j]);
                assert forall|q: int| j < q < o2.len() implies gt(o2[q].id, x.id) by { if q < n { assert(o2[q] == out[q]); } }
            }
        }
    }
}

pub open spec fn fits(list: List, ops: Seq<El>, out: List) -> bool {
    forall|p: int| 0 <= p < out.len() ==> list.contains(#[trigger] out[p]) || ops.contains(out[p])
}

pub proof fn lemma_valid_lam(list: List, ops: Seq<El>)
    requires valid_ops(list, ops),
    ensures lam(ops),
{
    assert forall|k: int| 0 <= k < ops.len() implies match (#[trigger] ops[k]).rf { None => true, Some(r) => idlt(r, ops[k].id) } by {
        assert(valid_ref(list, ops, ops[k]));
    }
}

// ids are unique across list and ops
pub proof fn lemma_ids_ops(list: List, ops: Seq<El>, x: El, y: El)
    requires valid_ops(list, ops), ops.contains(x), list.contains(y) || ops.contains(y), x.id == y.id,
    ensures x == y, ops.contains(y),
{
    let a = choose|a: int| 0 <= a < ops.len() && ops[a] == x;
    if list.contains(y) {
        let q = choose|q: int| 0 <= q < list.len() && list[q] == y;
        assert(contains_id(list, ops[a].id));
        assert(false);
    } else {
        let b = choose|b: int| 0 <= b < ops.len() && ops[b] == y;
        if a < b { assert(idlt(ops[a].id, ops[b].id)); }
        if b < a { assert(idlt(ops[b].id, ops[a].id)); }
    }
}

// the children of e (just placed at the end of out) satisfy the stack invariant over out.push(e)
pub proof fn lemma_kids_stack(list: List, ops: Seq<El>, out: List, e: El)
    requires inv(out), valid_ops(list, ops), fits(list, ops, out), !contains_id(out, e.id),
    ensures stack_inv(ops, out.push(e), kids(ops, Some(e.id))),
{
    lemma_valid_lam(list, ops);
    lemma_kids(ops, Some(e.id));
    let o2 = out.push(e);
    let n = out.len() as int;
    assert(o2[n] == e);
    let ks = kids(ops, Some(e.id));
    assert forall|k: int| 0 <= k < ks.len() implies
        ops.contains(#[trigger] ks[k]) && !contains_id(o2, ks[k].id) && cond(o2, ks[k]) by {
        let x = ks[k];
        assert(ops.contains(x) && x.rf == Some(e.id));
        let q = choose|q: int| 0 <= q < ops.len() && ops[q] == x;
        assert(idlt(e.id, x.id));
        assert(!contains_id(o2, x.id)) by {
            if contains_id(o2, x.id) {
                let p = choose|p: int| 0 <= p < o2.len() && o2[p].id == x.id;
                if p < n {
                    assert(o2[p] == out[p]);
                    assert(list.contains(out[p]) || ops.contains(out[p]));
                    lemma_ids_ops(list, ops, x, out[p]);
                    assert(out[p] == x);
                    lemma_ref_present(out, p);
                    assert(contains_id(out, e.id));
                } else { assert(o2[p] == e); }
            }
        }
        assert(cond(o2, x)) by {
            assert forall|q2: int| n < q2 < o2.len() implies gt(o2[q2].id, x.id) by {}
        }
    }
}

pub open spec fn above(e: El, b: Option<Id>) -> bool {
    match b { None => true, Some(x) => gt(e.id, x) }
}

pub proof fn lemma_contains_push(out: List, x: El)
    ensures out.push(x).contains(x), forall|y: El| out.contains(y) ==> out.push(x).contains(y),
{
    assert(out.push(x)[out.len() as int] == x);
    assert forall|y: El| out.contains(y) implies out.push(x).contains(y) by {
        let k = choose|k: int| 0 <= k < out.len() && out[k] == y;
        assert(out.push(x)[k] == y);
    }
}

pub proof fn lemma_cid_push(out: List, x: El, r: Id)
    requires !contains_id(out, r), x.id != r,
    ensures !contains_id(out.push(x), r),
{
    let o2 = out.push(x);
    if contains_id(o2, r) {
        let j = choose|j: int| 0 <= j < o2.len() && o2[j].id == r;
        if j < out.len() { assert(o2[j] == out[j]); assert(contains_id(out, r)); }
        else { assert(o2[j] == x); }
    }
}

// the pop loop: pops exactly down to n entries, keeps all invariants, and everything popped is above b
pub proof fn lemma_drain(list: List, ops: Seq<El>, stack: Seq<El>, n: nat, out: List, b: Option<Id>)
    requires
        valid_ops(list, ops), inv(out), fits(list, ops, out),
        stack_inv(ops, out, stack), jinv(ops, out, stack),
        n <= stack.len(),
        forall|k: int| n <= k < stack.len() ==> above(#[trigger] stack[k], b),
    ensures
        drain(ops, stack, n, out).0.len() == n,
        inv(drain(ops, stack, n, out).1),
        fits(list, ops, drain(ops, stack, n, out).1),
        stack_inv(ops, drain(ops, stack, n, out).1, drain(ops, stack, n, out).0),
        jinv(ops, drain(ops, stack, n, out).1, drain(ops, stack, n, out).0),
        forall|k: int| 0 <= k < n ==> drain(ops, stack, n, out).0[k] == stack[k],
        forall|k: int| 0 <= k < out.len() ==> drain(ops, stack, n, out).1[k] == out[k],
        drain(ops, stack, n, out).1.len() >= out.len(),
        forall|k: int| out.len() <= k < drain(ops, stack, n, out).1.len() ==>
            above(drain(ops, stack, n, out).1[k], b) && ops.contains(drain(ops, stack, n, out).1[k]),
    decreases cnt(ops, out),
{
    if stack.len() > n {
        let x = stack.last();
        let last = stack.len() - 1;
        assert(stack[last as int] == x);
        assert(ops.contains(x));
        assert(!out.contains(x)) by {
            if out.contains(x) { let k = choose|k: int| 0 <= k < out.len() && out[k] == x; assert(contains_id(out, x.id)); }
        }
        lemma_cnt_dec(ops, out, x);
        lemma_valid_lam(list, ops);
        let xi = choose|q: int| 0 <= q < ops.len() && ops[q] == x;
        assert(match x.rf { None => true, Some(r) => idlt(r, x.id) });
        assert(cond(out, x));
        let o2 = out.push(x);
        let base = stack.drop_last();
        let ks = kids(ops, Some(x.id));
        let s2 = base.add(ks);
        lemma_push_inv(out, x);
        lemma_contains_push(out, x);
        assert(fits(list, ops, o2)) by {
            assert forall|p: int| 0 <= p < o2.len() implies list.contains(#[trigger] o2[p]) || ops.contains(o2[p]) by {
                if p < out.len() { assert(o2[p] == out[p]); } else { assert(o2[p] == x); }
            }
        }
        assert(stack_inv(ops, out, base)) by {
            assert forall|a: int, b2: int| 0 <= a < b2 < base.len() implies idlt(base[a].id, base[b2].id) by { assert(base[a] == stack[a]); assert(base[b2] == stack[b2]); }
            assert forall|k: int| 0 <= k < base.len() implies
                ops.contains(#[trigger] base[k]) && !contains_id(out, base[k].id) && cond(out, base[k]) by { assert(base[k] == stack[k]); }
        }
        assert forall|k: int| 0 <= k < base.len() implies gt(x.id, #[trigger] base[k].id) by { assert(base[k] == stack[k]); }
        lemma_stack_push_out(ops, out, base, x);
        lemma_kids(ops, Some(x.id));
        lemma_kids_stack(list, ops, out, x);
        assert(stack_inv(ops, o2, s2)) by {
            assert forall|a: int, b2: int| 0 <= a < b2 < s2.len() implies idlt(s2[a].id, s2[b2].id) by {
                if b2 < base.len() { assert(s2[a] == base[a]); assert(s2[b2] == base[b2]); }
                else if a < base.len() {
                    assert(s2[a] == base[a]); assert(s2[b2] == ks[b2 - base.len()]);
                    assert(idlt(base[a].id, x.id));
                    assert(idlt(x.id, ks[b2 - base.len()].id));
                }
                else { assert(s2[a] == ks[a - base.len()]); assert(s2[b2] == ks[b2 - base.len()]); }
            }
            assert forall|k: int| 0 <= k < s2.len() implies
                ops.contains(#[trigger] s2[k]) && !contains_id(o2, s2[k].id) && cond(o2, s2[k]) by {
                if k < base.len() { assert(s2[k] == base[k]); } else { assert(s2[k] == ks[k - base.len()]); }
            }
        }
        assert(jinv(ops, o2, s2)) by {
            assert forall|k: int| 0 <= k < ops.len() implies {
                let y = #[trigger] ops[k];
                o2.contains(y) || s2.contains(y) || (match y.rf { None => false, Some(r) => !contains_id(o2, r) })
            } by {
                let y = ops[k];
                if out.contains(y) { }
                else if stack.contains(y) {
                    let q = choose|q: int| 0 <= q < stack.len() && stack[q] == y;
                    if q == last { assert(o2.contains(x)); }
                    else { assert(s2[q] == base[q]); assert(base[q] == stack[q]); }
                } else {
                    match y.rf {
                        None => {}
                        Some(r) => {
                            if !contains_id(out, r) {
                                if r == x.id {
                                    assert(ops.contains(y));
                                    assert(ks.contains(y));
                                    let q = choose|q: int| 0 <= q < ks.len() && ks[q] == y;
                                    assert(s2[base.len() + q] == y);
                                } else { lemma_cid_push(out, x, r); }
                            }
                        }
                    }
                }
            }
        }
        assert(n <= s2.len());
        assert forall|k: int| n <= k < s2.len() implies above(#[trigger] s2[k], b) by {
            if k < base.len() { assert(s2[k] == base[k]); assert(base[k] == stack[k]); }
            else {
                let kid = ks[k - base.len()];
                assert(s2[k] == kid);
                assert(above(x, b));
                assert(idlt(x.id, kid.id));
            }
        }
        lemma_drain(list, ops, s2, n, o2, b);
        let r = drain(ops, s2, n, o2);
        assert(drain(ops, stack, n, out) == r);
        assert forall|k: int| 0 <= k < n implies r.0[k] == stack[k] by { assert(s2[k] == base[k]); assert(base[k] == stack[k]); }
        assert forall|k: int| 0 <= k < out.len() implies r.1[k] == out[k] by { assert(o2[k] == out[k]); }
        assert forall|k: int| out.len() <= k < r.1.len() implies above(r.1[k], b) && ops.contains(r.1[k]) by {
            if k == out.len() { assert(r.1[k] == o2[k]); assert(o2[k] == x); assert(above(x, b)); }
        }
    } else {
        assert(drain(ops, stack, n, out) == (stack, out));
    }
}

pub proof fn lemma_pp(s: Seq<El>, id: Id)
    requires asc(s), forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).id != id,
    ensures
        pp(s, id) <= s.len(),
        forall|k: int| 0 <= k < pp(s, id) ==> idlt(s[k].id, id),
        forall|k: int| pp(s, id) <= k < s.len() ==> gt(s[k].id, id),
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        let l = s.len() - 1;
        if idlt(s.last().id, id) {
            assert forall|k: int| 0 <= k < s.len() implies idlt(s[k].id, id) by {
                if k < l { assert(idlt(s[k].id, s[l as int].id)); }
            }
        } else {
            assert(asc(t)) by { assert forall|a: int, b: int| 0 <= a < b < t.len() implies idlt(t[a].id, t[b].id) by { assert(t[a] == s[a]); assert(t[b] == s[b]); } }
            assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id != id by { assert(t[k] == s[k]); }
            lemma_pp(t, id);
            assert forall|k: int| 0 <= k < pp(t, id) implies idlt(s[k].id, id) by { assert(t[k] == s[k]); }
            assert forall|k: int| pp(t, id) <= k < s.len() implies gt(s[k].id, id) by { if k < t.len() { assert(t[k] == s[k]); } }
        }
    }
}

pub proof fn lemma_min_unplaced(ops: Seq<El>, out: List)
    requires exists|y: El| ops.contains(y) && !out.contains(y),
    ensures exists|z: El| ops.contains(z) && !out.contains(z)
        && forall|w: El| ops.contains(w) && !out.contains(w) ==> !idlt(w.id, z.id),
    decreases ops.len(),
{
    let t = ops.drop_last();
    let l = ops.last();
    assert(ops.len() > 0) by { let y = choose|y: El| ops.contains(y) && !out.contains(y); let k = choose|k: int| 0 <= k < ops.len() && ops[k] == y; }
    assert forall|w: El| t.contains(w) implies ops.contains(w) by { let k = choose|k: int| 0 <= k < t.len() && t[k] == w; assert(ops[k] == w); }
    assert(ops.contains(l)) by { assert(ops[ops.len() - 1] == l); }
    assert forall|w: El| ops.contains(w) implies t.contains(w) || w == l by {
        let k = choose|k: int| 0 <= k < ops.len() && ops[k] == w;
        if k < t.len() { assert(t[k] == w); }
    }
    if exists|y: El| t.contains(y) && !out.contains(y) {
        lemma_min_unplaced(t, out);
        let z = choose|z: El| t.contains(z) && !out.contains(z) && forall|w: El| t.contains(w) && !out.contains(w) ==> !idlt(w.id, z.id);
        if !out.contains(l) && idlt(l.id, z.id) {
            assert(forall|w: El| ops.contains(w) && !out.contains(w) ==> !idlt(w.id, l.id)) by {
                assert forall|w: El| ops.contains(w) && !out.contains(w) implies !idlt(w.id, l.id) by {
                    if w != l { assert(t.contains(w)); assert(!idlt(w.id, z.id)); }
                }
            }
        }
    } else {
        let y = choose|y: El| ops.contains(y) && !out.contains(y);
        assert(y == l);
    }
}

pub open spec fn winv(list: List, ops: Seq<El>, i: nat, out: List, stack: Seq<El>, dp: Seq<int>) -> bool {
    &&& valid_ops(list, ops)
    &&& i <= list.len()
    &&& dp.len() == i
    &&& forall|m: int| 0 <= m < i ==> 0 <= #[trigger] dp[m] < out.len() && out[dp[m]] == list[m]
    &&& forall|m: int, m2: int| 0 <= m < m2 < i ==> dp[m] < dp[m2]
    &&& forall|k: int| 0 <= k < out.len() ==>
            ((exists|m: int| 0 <= m < i && dp[m] == k) || ops.contains(#[trigger] out[k]))
    &&& forall|k: int| #![trigger out[k]] 0 <= k < out.len() ==>
            ((forall|m: int| 0 <= m < i ==> dp[m] != k)
                ==> exists|m: int| 0 <= m < i && dp[m] > k && gt(out[k].id, list[m].id))
    &&& inv(out)
    &&& stack_inv(ops, out, stack)
    &&& jinv(ops, out, stack)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(2000)]
pub proof fn lemma_walk(list: List, ops: Seq<El>, i: nat, out: List, stack: Seq<El>, dp: Seq<int>)
    requires winv(list, ops, i, out, stack, dp),
    ensures
        inv(walk(list, ops, i, out, stack)),
        fits(list, ops, walk(list, ops, i, out, stack)),
        forall|e: El| list.contains(e) || ops.contains(e) ==> walk(list, ops, i, out, stack).contains(e),
    decreases list.len() - i,
{
    assert(fits(list, ops, out)) by {
        assert forall|p: int| 0 <= p < out.len() implies list.contains(#[trigger] out[p]) || ops.contains(out[p]) by {
            if exists|m: int| 0 <= m < i && dp[m] == p {
                let m = choose|m: int| 0 <= m < i && dp[m] == p;
                assert(list[m] == out[p]);
            }
        }
    }
    if i >= list.len() {
        assert(i == list.len());
        lemma_drain(list, ops, stack, 0, out, None);
        let r = drain(ops, stack, 0, out);
        assert(walk(list, ops, i, out, stack) == r.1);
        // all list elements are in r.1
        assert forall|e: El| list.contains(e) implies r.1.contains(e) by {
            let m = choose|m: int| 0 <= m < list.len() && list[m] == e;
            assert(r.1[dp[m]] == out[dp[m]]);
        }
        assert forall|y: El| ops.contains(y) implies r.1.contains(y) by {
            if !r.1.contains(y) {
                assert(exists|z: El| ops.contains(z) && !r.1.contains(z));
                lemma_min_unplaced(ops, r.1);
                let z = choose|z: El| ops.contains(z) && !r.1.contains(z)
                    && forall|w: El| ops.contains(w) && !r.1.contains(w) ==> !idlt(w.id, z.id);
                let zi = choose|q: int| 0 <= q < ops.len() && ops[q] == z;
                assert(!r.0.contains(z)) by { assert(r.0.len() == 0); }
                assert(valid_ref(list, ops, z));
                match z.rf {
                    None => { assert(false); }
                    Some(rr) => {
                        assert(!contains_id(r.1, rr));
                        if contains_id(list, rr) {
                            let m = choose|m: int| 0 <= m < list.len() && list[m].id == rr;
                            assert(r.1[dp[m]] == out[dp[m]]);
                            assert(r.1[dp[m]].id == rr);
                            assert(contains_id(r.1, rr));
                        } else {
                            assert(contains_id(ops, rr));
                            let q = choose|q: int| 0 <= q < ops.len() && ops[q].id == rr;
                            let yy = ops[q];
                            assert(ops.contains(yy));
                            assert(idlt(yy.id, z.id));
                            assert(r.1.contains(yy));
                            let u = choose|u: int| 0 <= u < r.1.len() && r.1[u] == yy;
                            assert(contains_id(r.1, rr));
                        }
                    }
                }
            }
        }
    } else {
        let d = list[i as int];
        assert(ok_at(list, i as int));
        assert(valid_ops(list, ops));
        let n = pp(stack, d.id);
        assert forall|k: int| 0 <= k < stack.len() implies (#[trigger] stack[k]).id != d.id by {
            assert(ops.contains(stack[k]));
            let q = choose|q: int| 0 <= q < ops.len() && ops[q] == stack[k];
            if stack[k].id == d.id { assert(contains_id(list, ops[q].id)); }
        }
        lemma_pp(stack, d.id);
        lemma_drain(list, ops, stack, n, out, Some(d.id));
        let rr = drain(ops, stack, n, out);
        let s1 = rr.0;
        let o1 = rr.1;
        // d is fresh in o1
        assert(!contains_id(o1, d.id)) by {
            if contains_id(o1, d.id) {
                let q = choose|q: int| 0 <= q < o1.len() && o1[q].id == d.id;
                if q < out.len() {
                    assert(o1[q] == out[q]);
                    if exists|m: int| 0 <= m < i && dp[m] == q {
                        let m = choose|m: int| 0 <= m < i && dp[m] == q;
                        assert(list[m] == out[q]);
                        assert(list[m].id == d.id);
                        assert(m != i as int);
                    } else {
                        assert(ops.contains(out[q]));
                        let w = choose|w: int| 0 <= w < ops.len() && ops[w] == out[q];
                        assert(contains_id(list, ops[w].id));
                    }
                } else {
                    assert(ops.contains(o1[q]));
                    let w = choose|w: int| 0 <= w < ops.len() && ops[w] == o1[q];
                    assert(contains_id(list, ops[w].id));
                }
            }
        }
        // cond(o1, d)
        assert(cond(o1, d)) by {
            match d.rf {
                None => {
                    assert forall|k: int| 0 <= k < o1.len() implies gt(o1[k].id, d.id) by {
                        if k < out.len() {
                            assert(o1[k] == out[k]);
                            if exists|m: int| 0 <= m < i && dp[m] == k {
                                let m = choose|m: int| 0 <= m < i && dp[m] == k;
                                assert(list[m] == out[k]);
                            } else {
                                let m = choose|m: int| 0 <= m < i && dp[m] > k && gt(out[k].id, list[m].id);
                                assert(gt(list[m].id, d.id));
                            }
                        }
                    }
                }
                Some(r) => {
                    let j = choose|j: int| 0 <= j < i && list[j].id == r && (forall|k: int| j < k < i ==> gt(list[k].id, d.id));
                    let p = dp[j];
                    assert(o1[p] == out[p]);
                    assert(o1[p].id == r);
                    assert forall|k: int| p < k < o1.len() implies gt(o1[k].id, d.id) by {
                        if k < out.len() {
                            assert(o1[k] == out[k]);
                            if exists|m: int| 0 <= m < i && dp[m] == k {
                                let m = choose|m: int| 0 <= m < i && dp[m] == k;
                                assert(list[m] == out[k]);
                                if m <= j { if m == j { assert(false); } else { assert(dp[m] < dp[j]); } }
                                assert(gt(list[m].id, d.id));
                            } else {
                                let m = choose|m: int| 0 <= m < i && dp[m] > k && gt(out[k].id, list[m].id);
                                if m <= j { if m == j { assert(false); } else { assert(dp[m] < dp[j]); } }
                                assert(gt(list[m].id, d.id));
                            }
                        }
                    }
                }
            }
        }
        assert(match d.rf { None => true, Some(r) => idlt(r, d.id) });
        assert(fits(list, ops, o1));
        lemma_push_inv(o1, d);
        let o3 = o1.push(d);
        lemma_contains_push(o1, d);
        // stack over o3
        assert forall|k: int| 0 <= k < s1.len() implies gt(d.id, #[trigger] s1[k].id) by { assert(s1[k] == stack[k]); }
        lemma_stack_push_out(ops, o1, s1, d);
        lemma_kids(ops, Some(d.id));
        lemma_kids_stack(list, ops, o1, d);
        lemma_valid_lam(list, ops);
        let ks = kids(ops, Some(d.id));
        let s2 = s1.add(ks);
        assert(stack_inv(ops, o3, s2)) by {
            assert forall|a: int, b: int| 0 <= a < b < s2.len() implies idlt(s2[a].id, s2[b].id) by {
                if b < s1.len() { assert(s2[a] == s1[a]); assert(s2[b] == s1[b]); }
                else if a < s1.len() {
                    assert(s2[a] == s1[a]); assert(s2[b] == ks[b - s1.len()]);
                    assert(idlt(s1[a].id, d.id));
                    assert(idlt(d.id, ks[b - s1.len()].id));
                }
                else { assert(s2[a] == ks[a - s1.len()]); assert(s2[b] == ks[b - s1.len()]); }
            }
            assert forall|k: int| 0 <= k < s2.len() implies
                ops.contains(#[trigger] s2[k]) && !contains_id(o3, s2[k].id) && cond(o3, s2[k]) by {
                if k < s1.len() { assert(s2[k] == s1[k]); } else { assert(s2[k] == ks[k - s1.len()]); }
            }
        }
        assert(jinv(ops, o3, s2)) by {
            assert forall|k: int| 0 <= k < ops.len() implies {
                let y = #[trigger] ops[k];
                o3.contains(y) || s2.contains(y) || (match y.rf { None => false, Some(r) => !contains_id(o3, r) })
            } by {
                let y = ops[k];
                if o1.contains(y) { }
                else if s1.contains(y) {
                    let q = choose|q: int| 0 <= q < s1.len() && s1[q] == y;
                    assert(s2[q] == y);
                } else {
                    match y.rf {
                        None => {}
                        Some(r) => {
                            if !contains_id(o1, r) {
                                if r == d.id {
                                    assert(ops.contains(y));
                                    assert(ks.contains(y));
                                    let q = choose|q: int| 0 <= q < ks.len() && ks[q] == y;
                                    assert(s2[s1.len() + q] == y);
                                } else { lemma_cid_push(o1, d, r); }
                            }
                        }
                    }
                }
            }
        }
        let dp2 = dp.push(o1.len() as int);
        assert(o3[o1.len() as int] == d);
        assert(winv(list, ops, i + 1, o3, s2, dp2)) by {
            assert forall|m: int| 0 <= m < i + 1 implies 0 <= #[trigger] dp2[m] < o3.len() && o3[dp2[m]] == list[m] by {
                if m < i { assert(dp2[m] == dp[m]); assert(o3[dp[m]] == o1[dp[m]]); assert(o1[dp[m]] == out[dp[m]]); }
            }
            assert forall|m: int, m2: int| 0 <= m < m2 < i + 1 implies dp2[m] < dp2[m2] by {
                if m2 < i { assert(dp2[m] == dp[m]); assert(dp2[m2] == dp[m2]); }
                else { assert(dp2[m] == dp[m]); assert(dp[m] < out.len()); }
            }
            assert forall|k: int| 0 <= k < o3.len() implies
                ((exists|m: int| 0 <= m < i + 1 && dp2[m] == k) || ops.contains(#[trigger] o3[k])) by {
                if k < out.len() {
                    assert(o3[k] == out[k]);
                    if exists|m: int| 0 <= m < i && dp[m] == k { let m = choose|m: int| 0 <= m < i && dp[m] == k; assert(dp2[m] == k); }
                } else if k < o1.len() { assert(o3[k] == o1[k]); }
                else { assert(dp2[i as int] == k); }
            }
            assert forall|k: int| #![trigger o3[k]] 0 <= k < o3.len() implies
                ((forall|m: int| 0 <= m < i + 1 ==> dp2[m] != k)
                    ==> exists|m: int| 0 <= m < i + 1 && dp2[m] > k && gt(o3[k].id, list[m].id)) by {
                if forall|m: int| 0 <= m < i + 1 ==> dp2[m] != k {
                    if k < out.len() {
                        assert(o3[k] == out[k]);
                        assert(forall|m: int| 0 <= m < i ==> dp[m] != k) by { assert forall|m: int| 0 <= m < i implies dp[m] != k by { assert(dp2[m] == dp[m]); } }
                        let m = choose|m: int| 0 <= m < i && dp[m] > k && gt(out[k].id, list[m].id);
                        assert(dp2[m] == dp[m]);
                    } else if k < o1.len() {
                        assert(o3[k] == o1[k]);
                        assert(dp2[i as int] > k);
                        assert(gt(o1[k].id, d.id));
                    } else { assert(dp2[i as int] == k); }
                }
            }
        }
        lemma_walk(list, ops, i + 1, o3, s2, dp2);
        assert(walk(list, ops, i, out, stack) == walk(list, ops, i + 1, o3, s2));
    }
}

pub proof fn lemma_batch_facts(list: List, ops: Seq<El>)
    requires valid_ops(list, ops),
    ensures
        inv(batch_ins(list, ops)),
        fits(list, ops, batch_ins(list, ops)),
        forall|e: El| list.contains(e) || ops.contains(e) ==> batch_ins(list, ops).contains(e),
{
    let empty = Seq::<El>::empty();
    let st = kids(ops, None);
    lemma_kids(ops, None);
    assert(inv(empty));
    assert(stack_inv(ops, empty, st)) by {
        assert forall|k: int| 0 <= k < st.len() implies
            ops.contains(#[trigger] st[k]) && !contains_id(empty, st[k].id) && cond(empty, st[k]) by {
            assert(!contains_id(empty, st[k].id));
        }
    }
    assert(jinv(ops, empty, st)) by {
        assert forall|k: int| 0 <= k < ops.len() implies {
            let x = #[trigger] ops[k];
            empty.contains(x) || st.contains(x) || (match x.rf { None => false, Some(r) => !contains_id(empty, r) })
        } by {
            let x = ops[k];
            assert(ops.contains(x));
            match x.rf { None => { assert(st.contains(x)); } Some(r) => { assert(!contains_id(empty, r)); } }
        }
    }
    let dp = Seq::<int>::empty();
    assert(winv(list, ops, 0, empty, st, dp));
    lemma_walk(list, ops, 0, empty, st, dp);
}

// ---------- sequential application (the crdt_text.rs one-op model) ----------
pub open spec fn seq_ins(l: List, h: Seq<El>) -> List
    decreases h.len(),
{
    if h.len() == 0 { l } else { ins(seq_ins(l, h.drop_last()), h.last()) }
}

pub open spec fn causal(l: List, h: Seq<El>) -> bool
    decreases h.len(),
{
    if h.len() == 0 { true } else { causal(l, h.drop_last()) && ready(seq_ins(l, h.drop_last()), h.last()) }
}

pub proof fn lemma_seq_facts(l: List, h: Seq<El>)
    requires inv(l), causal(l, h),
    ensures
        inv(seq_ins(l, h)),
        forall|e: El| seq_ins(l, h).contains(e) <==> (l.contains(e) || h.contains(e)),
    decreases h.len(),
{
    if h.len() > 0 {
        let t = h.drop_last();
        lemma_seq_facts(l, t);
        let s = seq_ins(l, t);
        let e = h.last();
        lemma_ins_preserves(s, e);
        lemma_els_ins(s, e);
        assert forall|x: El| seq_ins(l, h).contains(x) <==> (l.contains(x) || h.contains(x)) by {
            assert(els(ins(s, e)).contains(x) == els(s).insert(e).contains(x));
            if h.contains(x) {
                let k = choose|k: int| 0 <= k < h.len() && h[k] == x;
                if k < t.len() { assert(t[k] == x); assert(t.contains(x)); }
                else { assert(x == e); }
            }
            if t.contains(x) { let k = choose|k: int| 0 <= k < t.len() && t[k] == x; assert(h[k] == x); }
            if x == e { assert(h[h.len() - 1] == e); }
        }
    }
}

pub proof fn lemma_inv_idunique(l: List)
    requires inv(l),
    ensures forall|x: El, y: El| l.contains(x) && l.contains(y) && x.id == y.id ==> x == y,
{
    assert forall|x: El, y: El| l.contains(x) && l.contains(y) && x.id == y.id implies x == y by {
        let i = choose|i: int| 0 <= i < l.len() && l[i] == x;
        let j = choose|j: int| 0 <= j < l.len() && l[j] == y;
        if i < j { assert(l[i].id != l[j].id); }
        if j < i { assert(l[j].id != l[i].id); }
    }
}

// Main theorem: the single-pass batch result equals sequential one-op application in ANY causal order of the ops.
pub proof fn theorem_batch_eq_seq(list: List, ops: Seq<El>, h: Seq<El>)
    requires
        valid_ops(list, ops),
        causal(list, h),
        forall|e: El| h.contains(e) <==> ops.contains(e),
    ensures
        seq_ins(list, h) == batch_ins(list, ops),
{
    lemma_seq_facts(list, h);
    lemma_batch_facts(list, ops);
    let a = seq_ins(list, h);
    let b = batch_ins(list, ops);
    assert(inv(a) && inv(b));
    assert forall|e: El| a.contains(e) == b.contains(e) by {
        if b.contains(e) {
            let k = choose|k: int| 0 <= k < b.len() && b[k] == e;
            assert(list.contains(b[k]) || ops.contains(b[k]));
            assert(h.contains(e) || list.contains(e));
        }
        if list.contains(e) || ops.contains(e) { assert(b.contains(e)); }
        if h.contains(e) { assert(ops.contains(e)); }
    }
    assert(els(a) =~= els(b));
    lemma_inv_idunique(a);
    lemma_unique(a, b);
}

// Corollary: order independence.
pub proof fn corollary_order_independent(list: List, ops: Seq<El>, h1: Seq<El>, h2: Seq<El>)
    requires
        valid_ops(list, ops),
        causal(list, h1), forall|e: El| h1.contains(e) <==> ops.contains(e),
        causal(list, h2), forall|e: El| h2.contains(e) <==> ops.contains(e),
    ensures seq_ins(list, h1) == seq_ins(list, h2),
{
    theorem_batch_eq_seq(list, ops, h1);
    theorem_batch_eq_seq(list, ops, h2);
}

// The id-sorted batch itself is a causal order, so at least one sequential order exists.
pub proof fn lemma_ops_causal(list: List, ops: Seq<El>)
    requires valid_ops(list, ops),
    ensures causal(list, ops),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let t = ops.drop_last();
        let n = t.len() as int;
        let e = ops.last();
        assert(ops[n] == e);
        assert forall|k: int| 0 <= k < t.len() implies valid_ref(list, t, #[trigger] t[k]) by {
            assert(t[k] == ops[k]);
            assert(valid_ref(list, ops, ops[k]));
            if let Some(r) = t[k].rf {
                if !contains_id(list, r) {
                    let q = choose|q: int| 0 <= q < ops.len() && ops[q].id == r;
                    assert(q != n) by { if q == n { assert(idlt(ops[k].id, ops[n].id)); } }
                    assert(t[q].id == r);
                }
            }
        }
        assert(valid_ops(list, t)) by {
            assert forall|a: int, b: int| 0 <= a < b < t.len() implies idlt(t[a].id, t[b].id) by { assert(t[a] == ops[a]); assert(t[b] == ops[b]); }
            assert forall|k: int| 0 <= k < t.len() implies !contains_id(list, (#[trigger] t[k]).id) by { assert(t[k] == ops[k]); }
        }
        lemma_ops_causal(list, t);
        lemma_seq_facts(list, t);
        let sl = seq_ins(list, t);
        assert(valid_ref(list, ops, e));
        assert(ready(sl, e)) by {
            assert(!contains_id(sl, e.id)) by {
                if contains_id(sl, e.id) {
                    let p = choose|p: int| 0 <= p < sl.len() && sl[p].id == e.id;
                    assert(sl.contains(sl[p]));
                    if t.contains(sl[p]) {
                        let q = choose|q: int| 0 <= q < t.len() && t[q] == sl[p];
                        assert(idlt(ops[q].id, ops[n].id));
                    } else {
                        assert(list.contains(sl[p]));
                        assert(contains_id(list, e.id)) by { let q = choose|q: int| 0 <= q < list.len() && list[q] == sl[p]; }
                    }
                }
            }
            if let Some(r) = e.rf {
                if contains_id(list, r) {
                    let q = choose|q: int| 0 <= q < list.len() && list[q].id == r;
                    assert(list.contains(list[q]));
                    assert(sl.contains(list[q]));
                    let u = choose|u: int| 0 <= u < sl.len() && sl[u] == list[q];
                    assert(sl[u].id == r);
                } else {
                    let q = choose|q: int| 0 <= q < ops.len() && ops[q].id == r;
                    assert(q != n);
                    assert(t[q] == ops[q]);
                    assert(t.contains(t[q]));
                    assert(sl.contains(t[q]));
                    let u = choose|u: int| 0 <= u < sl.len() && sl[u] == t[q];
                    assert(sl[u].id == r);
                }
            }
        }
    }
}

pub proof fn corollary_batch_eq_idsorted(list: List, ops: Seq<El>)
    requires valid_ops(list, ops),
    ensures seq_ins(list, ops) == batch_ins(list, ops),
{
    lemma_ops_causal(list, ops);
    theorem_batch_eq_seq(list, ops, ops);
}

// ============================ example_run ============================
// doc = [A, B] (B is a child of A).  Batch (sorted by id):
//   T(2,1) and R(6,1) after HEAD, P(4,2) after A (concurrent with B, P.id > B.id), Q(5,3) after P (gosub),
//   S(7,2) after B (drained at the end).
// Expected RGA order: R, T, A, P, Q, B, S.
pub open spec fn ea() -> El { El { id: (1, 1), rf: None, ch: 65 } }
pub open spec fn eb() -> El { El { id: (3, 1), rf: Some((1, 1)), ch: 66 } }
pub open spec fn et() -> El { El { id: (2, 1), rf: None, ch: 84 } }
pub open spec fn ep() -> El { El { id: (4, 2), rf: Some((1, 1)), ch: 80 } }
pub open spec fn eq_() -> El { El { id: (5, 3), rf: Some((4, 2)), ch: 81 } }
pub open spec fn er() -> El { El { id: (6, 1), rf: None, ch: 82 } }
pub open spec fn es() -> El { El { id: (7, 2), rf: Some((3, 1)), ch: 83 } }

pub proof fn example_run()
    ensures
        valid_ops(seq![ea(), eb()], seq![et(), ep(), eq_(), er(), es()]),
        batch_ins(seq![ea(), eb()], seq![et(), ep(), eq_(), er(), es()]) == seq![er(), et(), ea(), ep(), eq_(), eb(), es()],
        seq_ins(seq![ea(), eb()], seq![et(), ep(), eq_(), er(), es()]) == seq![er(), et(), ea(), ep(), eq_(), eb(), es()],
{
    let list = seq![ea(), eb()];
    let ops = seq![et(), ep(), eq_(), er(), es()];
    assert(list[0] == ea() && list[1] == eb());
    assert(contains_id(list, (1, 1))) by { assert(list[0].id == (1, 1)); }
    assert(contains_id(list, (3, 1))) by { assert(list[1].id == (3, 1)); }
    assert(inv(list)) by {
        assert(ok_at(list, 0));
        assert(ok_at(list, 1)) by { assert(list[0].id == (1, 1)); }
    }
    assert(valid_ops(list, ops)) by {
        assert forall|k: int| 0 <= k < ops.len() implies valid_ref(list, ops, #[trigger] ops[k]) by {
            if k == 2 { assert(ops[1].id == (4, 2)); assert(contains_id(ops, (4, 2))); }
        }
        assert forall|k: int| 0 <= k < ops.len() implies !contains_id(list, (#[trigger] ops[k]).id) by {
            assert forall|j: int| 0 <= j < list.len() implies list[j].id != ops[k].id by {}
        }
    }
    let exp = seq![er(), et(), ea(), ep(), eq_(), eb(), es()];
    assert(batch_ins(list, ops) == exp) by {
        reveal_with_fuel(kids, 7);
        reveal_with_fuel(cnt, 7);
        reveal_with_fuel(pp, 4);
        reveal_with_fuel(drain, 5);
        reveal_with_fuel(walk, 4);
    }
    corollary_batch_eq_idsorted(list, ops);
}

fn main() {}

} // verus!
