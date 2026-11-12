// NEGATIVE CONTROL (expect errors): PredCache consumed only by doc ops (drop Untangler::new batch.rs:269): deletes of elements inserted in the same batch are lost.
// Mixed batches (inserts + deletes), marks, counters. See BATCH_STATUS.md.
// Reuses crdt_batch.rs unchanged as module `b` (its theorem_batch_eq_seq is the insert part).
use vstd::prelude::*;
#[path = "../crdt_batch.rs"]
#[allow(dead_code)]
mod b;
use b::*;

verus! {

// ===================== Part 1: a change batch with inserts AND deletes =====================
// One-op model (crdt_text.rs): Ins(e) = RGA insert; Del{d, t} = op d whose pred is element t
// (adds succ pair (t, d); an element is deleted iff it has a non-increment succ).
pub enum Op {
    Ins(El),
    Del { d: Id, t: Id },
}

pub struct St {
    pub list: List,
    pub succ: ISet<(Id, Id)>, // (target, deleter)
}

pub open spec fn apply1(s: St, o: Op) -> St {
    match o {
        Op::Ins(e) => St { list: ins(s.list, e), succ: s.succ },
        Op::Del { d, t } => St { list: s.list, succ: s.succ.insert((t, d)) },
    }
}

pub open spec fn seq_apply(s: St, h: Seq<Op>) -> St
    decreases h.len(),
{
    if h.len() == 0 { s } else { apply1(seq_apply(s, h.drop_last()), h.last()) }
}

// causal one-op history: each insert is ready; each delete's target is present when applied
pub open spec fn ok1(s: St, o: Op) -> bool {
    match o {
        Op::Ins(e) => ready(s.list, e),
        Op::Del { d, t } => contains_id(s.list, t),
    }
}

pub open spec fn causal_h(s: St, h: Seq<Op>) -> bool
    decreases h.len(),
{
    if h.len() == 0 { true } else { causal_h(s, h.drop_last()) && ok1(seq_apply(s, h.drop_last()), h.last()) }
}

pub open spec fn ins_of(h: Seq<Op>) -> Seq<El>
    decreases h.len(),
{
    if h.len() == 0 { Seq::empty() } else {
        match h.last() {
            Op::Ins(e) => ins_of(h.drop_last()).push(e),
            Op::Del { .. } => ins_of(h.drop_last()),
        }
    }
}

pub open spec fn dels_of(h: Seq<Op>) -> ISet<(Id, Id)> {
    ISet::new(|p: (Id, Id)| h.contains(Op::Del { d: p.1, t: p.0 }))
}

// ---- the real batch path, modelled ----
// PredCache (batch.rs:19 `SmallHashMap<OpId, Vec<(OpId, Option<i64>)>>`): target -> deleters,
// built by one pass over the change ops.
pub open spec fn pc(h: Seq<Op>) -> Map<Id, Seq<Id>>
    decreases h.len(),
{
    if h.len() == 0 { Map::empty() } else {
        let m = pc(h.drop_last());
        match h.last() {
            Op::Ins(_) => m,
            Op::Del { d, t } => {
                let old = if m.contains_key(t) { m[t] } else { Seq::empty() };
                m.insert(t, old.push(d))
            }
        }
    }
}

// Consumption: Untangler::new (batch.rs:269 `pred.remove(&op.id())` for change ops) and
// handle_doc_op/process_pred (batch.rs:70, 484 `pred.remove(&d.id)` for doc ops) each push
// (d.id, deleter) for every entry of an element they meet; every element of the result is met once.
pub open spec fn consumed(m: Map<Id, Seq<Id>>, out: List) -> ISet<(Id, Id)> {
    ISet::new(|p: (Id, Id)| m.contains_key(p.0) && m[p.0].contains(p.1) && contains_id(out, p.0))
}

pub open spec fn batch_apply(s: St, batch: Seq<Op>) -> St {
    let out = batch_ins(s.list, ins_of(batch));
    St { list: out, succ: s.succ.union(consumed(pc(batch), s.list)) }
}

pub open spec fn valid_batch(s: St, batch: Seq<Op>) -> bool {
    &&& valid_ops(s.list, ins_of(batch))   // incl. ids sorted (order_ops_for_doc, batch.rs:919)
    // every delete target exists in the list or among the batch's inserts
    &&& forall|d: Id, t: Id| batch.contains(Op::Del { d, t }) ==> contains_id(s.list, t) || contains_id(ins_of(batch), t)
}

// ---- lemmas ----
pub proof fn lemma_ins_of(h: Seq<Op>)
    ensures forall|e: El| ins_of(h).contains(e) <==> h.contains(Op::Ins(e)),
    decreases h.len(),
{
    if h.len() > 0 {
        let t = h.drop_last();
        lemma_ins_of(t);
        assert forall|e: El| ins_of(h).contains(e) <==> h.contains(Op::Ins(e)) by {
            if h.contains(Op::Ins(e)) {
                let k = choose|k: int| 0 <= k < h.len() && h[k] == Op::Ins(e);
                if k < t.len() { assert(t[k] == Op::Ins(e)); assert(t.contains(Op::Ins(e))); }
            }
            if t.contains(Op::Ins(e)) { let k = choose|k: int| 0 <= k < t.len() && t[k] == Op::Ins(e); assert(h[k] == t[k]); }
            match h.last() {
                Op::Ins(x) => {
                    let s = ins_of(t);
                    if s.contains(e) { let k = choose|k: int| 0 <= k < s.len() && s[k] == e; assert(s.push(x)[k] == e); }
                    if ins_of(h).contains(e) {
                        let k = choose|k: int| 0 <= k < s.len() + 1 && s.push(x)[k] == e;
                        if k < s.len() { assert(s[k] == e); assert(s.contains(e)); } else { assert(h[h.len() - 1] == Op::Ins(e)); }
                    }
                    if e == x { assert(s.push(x)[s.len() as int] == e); }
                }
                Op::Del { .. } => {}
            }
        }
    }
}

pub proof fn lemma_contains_id_iff(l: Seq<El>, id: Id)
    ensures contains_id(l, id) <==> exists|e: El| l.contains(e) && e.id == id,
{
    if contains_id(l, id) {
        let k = choose|k: int| 0 <= k < l.len() && l[k].id == id;
        assert(l.contains(l[k]));
    }
    if exists|e: El| l.contains(e) && e.id == id {
        let e = choose|e: El| l.contains(e) && e.id == id;
        let k = choose|k: int| 0 <= k < l.len() && l[k] == e;
        assert(l[k].id == id);
    }
}

// one-op fold splits into: list = sequential RGA insert of the insert subsequence; succ = union of deletes
pub proof fn lemma_split(s: St, h: Seq<Op>)
    requires causal_h(s, h),
    ensures
        seq_apply(s, h).list == seq_ins(s.list, ins_of(h)),
        causal(s.list, ins_of(h)),
        seq_apply(s, h).succ == s.succ.union(dels_of(h)),
    decreases h.len(),
{
    if h.len() > 0 {
        let t = h.drop_last();
        lemma_split(s, t);
        match h.last() {
            Op::Ins(e) => {
                let it = ins_of(t);
                assert(it.push(e).drop_last() =~= it);
                assert(it.push(e).last() == e);
            }
            Op::Del { d, t: tg } => {}
        }
        assert(seq_apply(s, h).succ =~= s.succ.union(dels_of(h))) by {
            assert forall|p: (Id, Id)| h.contains(Op::Del { d: p.1, t: p.0 }) <==>
                (t.contains(Op::Del { d: p.1, t: p.0 }) || h.last() == Op::Del { d: p.1, t: p.0 }) by {
                let o = Op::Del { d: p.1, t: p.0 };
                if h.contains(o) {
                    let k = choose|k: int| 0 <= k < h.len() && h[k] == o;
                    if k < t.len() { assert(t[k] == o); }
                }
                if t.contains(o) { let k = choose|k: int| 0 <= k < t.len() && t[k] == o; assert(h[k] == o); }
                if h.last() == o { assert(h[h.len() - 1] == o); }
            }
        }
    }
}

pub proof fn lemma_pc(h: Seq<Op>)
    ensures forall|t: Id, d: Id| (pc(h).contains_key(t) && pc(h)[t].contains(d)) <==> h.contains(Op::Del { d, t }),
    decreases h.len(),
{
    if h.len() > 0 {
        let tl = h.drop_last();
        lemma_pc(tl);
        let m = pc(tl);
        assert forall|t: Id, d: Id| (pc(h).contains_key(t) && pc(h)[t].contains(d)) <==> h.contains(Op::Del { d, t }) by {
            let o = Op::Del { d, t };
            if h.contains(o) {
                let k = choose|k: int| 0 <= k < h.len() && h[k] == o;
                if k < tl.len() { assert(tl[k] == o); assert(tl.contains(o)); }
            }
            if tl.contains(o) { let k = choose|k: int| 0 <= k < tl.len() && tl[k] == o; assert(h[k] == o); }
            match h.last() {
                Op::Ins(_) => {}
                Op::Del { d: d2, t: t2 } => {
                    let old = if m.contains_key(t2) { m[t2] } else { Seq::empty() };
                    if t == t2 {
                        if old.contains(d) { let k = choose|k: int| 0 <= k < old.len() && old[k] == d; assert(old.push(d2)[k] == d); }
                        if old.push(d2).contains(d) {
                            let k = choose|k: int| 0 <= k < old.len() + 1 && old.push(d2)[k] == d;
                            if k < old.len() { assert(old[k] == d); assert(old.contains(d)); }
                        }
                        if d == d2 { assert(old.push(d2)[old.len() as int] == d); assert(h[h.len() - 1] == o); }
                    }
                }
            }
        }
    }
}

// MAIN: applying a whole change batch (inserts via the Untangler model, deletes via PredCache)
// equals applying its ops one at a time, in ANY causal order h of the same ops.
pub proof fn theorem_mixed_batch_eq_seq(s: St, batch: Seq<Op>, h: Seq<Op>)
    requires
        valid_batch(s, batch),
        causal_h(s, h),
        forall|o: Op| h.contains(o) <==> batch.contains(o),
    ensures
        seq_apply(s, h) == batch_apply(s, batch),
{
    lemma_split(s, h);
    lemma_ins_of(h);
    lemma_ins_of(batch);
    let ih = ins_of(h);
    let ib = ins_of(batch);
    assert forall|e: El| ih.contains(e) <==> ib.contains(e) by {
        assert(h.contains(Op::Ins(e)) == batch.contains(Op::Ins(e)));
    }
    theorem_batch_eq_seq(s.list, ib, ih);
    let out = batch_ins(s.list, ib);
    lemma_batch_facts(s.list, ib);
    lemma_pc(batch);
    assert(dels_of(h) =~= consumed(pc(batch), out)) by {
        assert forall|p: (Id, Id)| dels_of(h).contains(p) <==> consumed(pc(batch), out).contains(p) by {
            let o = Op::Del { d: p.1, t: p.0 };
            assert(h.contains(o) == batch.contains(o));
            if batch.contains(o) {
                // target present in out: it is in list or in the batch inserts, both end up in out
                lemma_contains_id_iff(s.list, p.0);
                lemma_contains_id_iff(ib, p.0);
                lemma_contains_id_iff(out, p.0);
                if contains_id(s.list, p.0) {
                    let e = choose|e: El| s.list.contains(e) && e.id == p.0;
                    assert(out.contains(e));
                } else {
                    let e = choose|e: El| ib.contains(e) && e.id == p.0;
                    assert(out.contains(e));
                }
            }
        }
    }
    assert(seq_apply(s, h).succ =~= batch_apply(s, batch).succ);
}

pub proof fn corollary_mixed_order_independent(s: St, batch: Seq<Op>, h1: Seq<Op>, h2: Seq<Op>)
    requires
        valid_batch(s, batch),
        causal_h(s, h1), causal_h(s, h2),
        forall|o: Op| h1.contains(o) <==> batch.contains(o),
        forall|o: Op| h2.contains(o) <==> batch.contains(o),
    ensures seq_apply(s, h1) == seq_apply(s, h2),
{
    theorem_mixed_batch_eq_seq(s, batch, h1);
    theorem_mixed_batch_eq_seq(s, batch, h2);
}

// ===================== Part 2a: marks =====================
// Text marks are sequence elements with action Mark and width 0 (op_set2/op.rs:200-204
// `SequenceType::Text if self.is_mark() => 0`). Model: ch == 0 marks a mark element; real chars have ch > 0.
// The RGA theorems above quantify over any `ch`, so marks converge like characters.
pub open spec fn is_mark(e: El) -> bool { e.ch == 0 }

pub open spec fn visible(l: List, succ: ISet<(Id, Id)>) -> Seq<nat>
    decreases l.len(),
{
    if l.len() == 0 { Seq::empty() } else {
        let r = visible(l.drop_last(), succ);
        let e = l.last();
        if is_mark(e) || (exists|d: Id| succ.contains((e.id, d))) { r } else { r.push(e.ch) }
    }
}

pub proof fn lemma_visible_insert_mark(l: List, k: int, m: El, succ: ISet<(Id, Id)>)
    requires 0 <= k <= l.len(), is_mark(m),
    ensures visible(l.insert(k, m), succ) == visible(l, succ),
    decreases l.len(),
{
    if k < l.len() {
        let t = l.drop_last();
        lemma_visible_insert_mark(t, k, m, succ);
        assert(l.insert(k, m).drop_last() =~= t.insert(k, m));
        assert(l.insert(k, m).last() == l.last());
    } else {
        assert(l.insert(k, m).drop_last() =~= l);
        assert(l.insert(k, m).last() == m);
    }
}

// A received mark changes no visible text (one-op model).
pub proof fn theorem_mark_preserves_text(s: St, m: El)
    requires is_mark(m), inv(s.list), ready(s.list, m),
    ensures visible(apply1(s, Op::Ins(m)).list, s.succ) == visible(s.list, s.succ),
{
    match m.rf { None => {}, Some(r) => { assert(0 <= idx(s.list, r) < s.list.len()); } }
    let k = slot(s.list, m);
    lemma_scan(s.list, start(s.list, m), m.id);
    lemma_visible_insert_mark(s.list, k, m, s.succ);
}

// Text (with marks) converges: equal op sets in any causal order give equal visible text.
pub proof fn corollary_text_converges(s: St, batch: Seq<Op>, h1: Seq<Op>, h2: Seq<Op>)
    requires
        valid_batch(s, batch),
        causal_h(s, h1), causal_h(s, h2),
        forall|o: Op| h1.contains(o) <==> batch.contains(o),
        forall|o: Op| h2.contains(o) <==> batch.contains(o),
    ensures
        visible(seq_apply(s, h1).list, seq_apply(s, h1).succ) == visible(seq_apply(s, h2).list, seq_apply(s, h2).succ),
{
    corollary_mixed_order_independent(s, batch, h1, h2);
}

// ===================== Part 2b: counters =====================
// Counter value = put value + sum of increments whose pred contains it (batch.rs do_increment:610).
// An increment is an op (id, delta). Delivery order of distinct increments does not matter.
pub open spec fn sum(h: Seq<(Id, int)>) -> int
    decreases h.len(),
{
    if h.len() == 0 { 0 } else { sum(h.drop_last()) + h.last().1 }
}

pub proof fn lemma_sum_remove(h: Seq<(Id, int)>, k: int)
    requires 0 <= k < h.len(),
    ensures sum(h) == sum(h.remove(k)) + h[k].1,
    decreases h.len(),
{
    if k < h.len() - 1 {
        let t = h.drop_last();
        lemma_sum_remove(t, k);
        assert(h.remove(k).drop_last() =~= t.remove(k));
        assert(h.remove(k).last() == h.last());
    } else {
        assert(h.remove(k) =~= h.drop_last());
    }
}

pub open spec fn distinct(h: Seq<(Id, int)>) -> bool {
    forall|a: int, b: int| 0 <= a < b < h.len() ==> h[a] != h[b]
}

pub proof fn theorem_counter_converges(base: int, h1: Seq<(Id, int)>, h2: Seq<(Id, int)>)
    requires
        distinct(h1), distinct(h2),
        forall|x: (Id, int)| h1.contains(x) <==> h2.contains(x),
    ensures base + sum(h1) == base + sum(h2),
    decreases h1.len(),
{
    if h1.len() == 0 {
        if h2.len() > 0 { assert(h2.contains(h2[0])); }
    } else {
        let x = h1.last();
        assert(h1.contains(x)) by { assert(h1[h1.len() - 1] == x); }
        let k = choose|k: int| 0 <= k < h2.len() && h2[k] == x;
        lemma_sum_remove(h2, k);
        let t1 = h1.drop_last();
        let t2 = h2.remove(k);
        assert forall|y: (Id, int)| t1.contains(y) <==> t2.contains(y) by {
            if t1.contains(y) {
                let i = choose|i: int| 0 <= i < t1.len() && t1[i] == y;
                assert(h1[i] == y); assert(y != x);
                assert(h1.contains(y)); assert(h2.contains(y));
                let j = choose|j: int| 0 <= j < h2.len() && h2[j] == y;
                assert(j != k); if j < k { assert(t2[j] == h2[j]); assert(t2.contains(y)); } else { assert(t2[j - 1] == h2[j]); assert(t2.contains(y)); }
            }
            if t2.contains(y) {
                let j = choose|j: int| 0 <= j < t2.len() && t2[j] == y;
                let jj = if j < k { j } else { j + 1 };
                assert(h2[jj] == y); assert(jj != k);
                assert(h2[jj] != h2[k]);
                assert(y != x);
                assert(h2.contains(y)); assert(h1.contains(y));
                let i = choose|i: int| 0 <= i < h1.len() && h1[i] == y;
                assert(i != h1.len() - 1);
                assert(t1[i] == y);
                assert(t1.contains(y));
            }
        }
        assert(distinct(t2)) by {
            assert forall|a: int, b: int| 0 <= a < b < t2.len() implies t2[a] != t2[b] by {
                let aa = if a < k { a } else { a + 1 };
                let bb = if b < k { b } else { b + 1 };
                assert(t2[a] == h2[aa]); assert(t2[b] == h2[bb]);
            }
        }
        theorem_counter_converges(base, t1, t2);
    }
}

fn main() {}

} // verus!
