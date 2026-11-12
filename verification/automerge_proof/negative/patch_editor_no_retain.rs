// NEGATIVE: daemon without file_deltas.retain. Must fail.
// Patch fidelity: TeamTypeV's cache fold (document.rs receive_sync_message_log_patches,
// replaced_text_objects_as_puts, types.rs PatchEffect::from_patch) and the daemon's editor
// delta list (daemon.rs ReceiveSyncMessage) end at the Automerge doc's text, per key,
// given the Automerge patch contract `am_contract` (trusted; see PATCH_DESIGN.md).
use vstd::prelude::*;

verus! {

pub enum Val { Text(nat, Seq<char>), Bytes(Seq<u8>), Absent }
pub enum Edit { Splice(nat, Seq<char>), Del(nat, nat) }
pub enum Act { PutText(nat), PutBytes(Seq<u8>), PutOther, DelMap, Conflict, Ed(Edit) }
pub struct P { pub key: int, pub act: Act }
pub enum Cache { Str(Seq<char>), Bytes(Seq<u8>), Missing }

// TextDelta [retain i, insert v] / [retain i, delete n] applied by TextDelta::apply_to
// (code points; Automerge 0.10 default TextEncoding::UnicodeCodePoint). None = Err (panic).
pub open spec fn apply(s: Seq<char>, e: Edit) -> Option<Seq<char>> {
    match e {
        Edit::Splice(i, v) => if i <= s.len() {
            Some(s.subrange(0, i as int) + v + s.subrange(i as int, s.len() as int)) } else { None },
        Edit::Del(i, n) => if i + n <= s.len() {
            Some(s.subrange(0, i as int) + s.subrange((i + n) as int, s.len() as int)) } else { None },
    }
}

pub open spec fn fold(s: Seq<char>, es: Seq<Edit>) -> Option<Seq<char>> decreases es.len() {
    if es.len() == 0 { Some(s) } else {
        match fold(s, es.drop_last()) { Some(t) => apply(t, es.last()), None => None }
    }
}

pub open spec fn is_map(a: Act) -> bool { !(a is Ed) }

// Edits for key k, in order.
pub open spec fn edits_of(ps: Seq<P>, k: int) -> Seq<Edit> decreases ps.len() {
    if ps.len() == 0 { seq![] } else {
        let r = edits_of(ps.drop_last(), k);
        match ps.last().act { Act::Ed(e) => if ps.last().key == k { r.push(e) } else { r }, _ => r }
    }
}

// replaced_text_objects_as_puts: Conflict whose visible text object changed -> PutText.
// before(k) is Text(w, _) iff k is in visible_text_objects (cache == doc before).
pub open spec fn convert(p: P, before: spec_fn(int) -> Val, after: spec_fn(int) -> Val) -> P {
    if p.act is Conflict && after(p.key) is Text && before(p.key) is Text
        && before(p.key)->Text_0 != after(p.key)->Text_0 {
        P { key: p.key, act: Act::PutText(after(p.key)->Text_0) }
    } else { p }
}

// One cache update (PatchEffect::from_patch then the match in receive_sync_message_log_patches),
// projected to key k. PutText/DelMap/PutOther -> FileRemoval; FileRemoval inserts "" iff the
// file is a text object in the (final) doc, else removes; Conflict -> NoEffect.
pub open spec fn step(c: Cache, p: P, k: int, after: spec_fn(int) -> Val) -> Option<Cache> {
    if p.key != k { Some(c) } else {
        match p.act {
            Act::PutText(_) | Act::PutOther | Act::DelMap =>
                Some(if after(k) is Text { Cache::Str(seq![]) } else { Cache::Missing }),
            Act::PutBytes(b) => Some(Cache::Bytes(b)),
            Act::Conflict => Some(c),
            Act::Ed(e) => {
                let old = match c { Cache::Str(s) => s, _ => seq![] };
                match apply(old, e) { Some(t) => Some(Cache::Str(t)), None => None }
            }
        }
    }
}

pub open spec fn cfold(c: Cache, ps: Seq<P>, k: int, before: spec_fn(int) -> Val,
    after: spec_fn(int) -> Val) -> Option<Cache> decreases ps.len() {
    if ps.len() == 0 { Some(c) } else {
        match cfold(c, ps.drop_last(), k, before, after) {
            Some(c1) => step(c1, convert(ps.last(), before, after), k, after),
            None => None,
        }
    }
}

pub open spec fn cache_of(v: Val) -> Cache {
    match v { Val::Text(_, t) => Cache::Str(t), Val::Bytes(b) => Cache::Bytes(b), Val::Absent => Cache::Missing }
}

pub open spec fn resets(p: P, k: int, before: spec_fn(int) -> Val, after: spec_fn(int) -> Val) -> bool {
    p.key == k && (convert(p, before, after).act is PutText || p.act is DelMap || p.act is PutOther)
}

// Last non-Conflict map action for k.
pub open spec fn lnc(ps: Seq<P>, k: int) -> Option<Act> decreases ps.len() {
    if ps.len() == 0 { None } else if ps.last().key == k && is_map(ps.last().act)
        && !(ps.last().act is Conflict) { Some(ps.last().act) } else { lnc(ps.drop_last(), k) }
}

// TRUSTED: Automerge patch contract for one sync message (PATCH_DESIGN.md).
pub open spec fn am_contract(ps: Seq<P>, m: int, k: int, before: spec_fn(int) -> Val,
    after: spec_fn(int) -> Val) -> bool {
    &&& 0 <= m <= ps.len()
    &&& forall|i: int| 0 <= i < m ==> is_map(#[trigger] ps[i].act)
    &&& forall|i: int| m <= i < ps.len() ==> (#[trigger] ps[i].act) is Ed
    &&& {
        let maps = ps.subrange(0, m);
        let es = edits_of(ps.subrange(m, ps.len() as int), k);
        match after(k) {
            Val::Text(o, t) => {
                &&& forall|i: int| 0 <= i < m && #[trigger] ps[i].key == k ==>
                        !(ps[i].act is PutBytes) && !(ps[i].act is PutOther)
                &&& if exists|i: int| 0 <= i < m && #[trigger] resets(ps[i], k, before, after) {
                        fold(seq![], es) == Some(t)
                    } else {
                        before(k) is Text && before(k)->Text_0 == o
                            && fold(before(k)->Text_1, es) == Some(t)
                    }
            }
            Val::Bytes(b) => es.len() == 0 && (lnc(maps, k) == Some(Act::PutBytes(b))
                || (lnc(maps, k) is None && before(k) == Val::Bytes(b))),
            Val::Absent => es.len() == 0 && (match lnc(maps, k) {
                Some(Act::PutBytes(_)) => false, Some(_) => true, None => before(k) is Absent }),
        }
    }
}

proof fn lemma_append(c: Cache, a: Seq<P>, b: Seq<P>, k: int, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    ensures cfold(c, a + b, k, be, af) == match cfold(c, a, k, be, af) {
        Some(c1) => cfold(c1, b, k, be, af), None => None }
    decreases b.len()
{
    if b.len() == 0 { assert(a + b =~= a); } else {
        lemma_append(c, a, b.drop_last(), k, be, af);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        match cfold(c, a, k, be, af) { Some(c1) => {}, None => {} }
    }
}

proof fn lemma_text_maps(c: Cache, ps: Seq<P>, k: int, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires af(k) is Text,
        forall|i: int| 0 <= i < ps.len() ==> is_map(#[trigger] ps[i].act),
        forall|i: int| 0 <= i < ps.len() && #[trigger] ps[i].key == k ==>
            !(ps[i].act is PutBytes) && !(ps[i].act is PutOther),
    ensures cfold(c, ps, k, be, af) == Some(
        if exists|i: int| 0 <= i < ps.len() && #[trigger] resets(ps[i], k, be, af) { Cache::Str(seq![]) } else { c })
    decreases ps.len()
{
    if ps.len() > 0 {
        let q = ps.drop_last();
        assert forall|i: int| 0 <= i < q.len() implies is_map(#[trigger] q[i].act) by { assert(q[i] == ps[i]); }
        assert forall|i: int| 0 <= i < q.len() && #[trigger] q[i].key == k implies
            !(q[i].act is PutBytes) && !(q[i].act is PutOther) by { assert(q[i] == ps[i]); }
        lemma_text_maps(c, q, k, be, af);
        let l = ps.len() - 1;
        assert(ps.last() == ps[l]);
        if exists|i: int| 0 <= i < ps.len() && #[trigger] resets(ps[i], k, be, af) {
            if !(exists|i: int| 0 <= i < q.len() && #[trigger] resets(q[i], k, be, af)) {
                let i = choose|i: int| 0 <= i < ps.len() && #[trigger] resets(ps[i], k, be, af);
                if i < l { assert(q[i] == ps[i]); assert(resets(q[i], k, be, af)); }
            } else {
                let i = choose|i: int| 0 <= i < q.len() && #[trigger] resets(q[i], k, be, af);
                assert(q[i] == ps[i]); assert(resets(ps[i], k, be, af));
            }
        } else {
            assert forall|i: int| 0 <= i < q.len() implies !#[trigger] resets(q[i], k, be, af) by {
                assert(q[i] == ps[i]); assert(!resets(ps[i], k, be, af)); }
            assert(!resets(ps[l], k, be, af));
        }
    }
}

proof fn lemma_other_maps(c: Cache, ps: Seq<P>, k: int, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires !(af(k) is Text), forall|i: int| 0 <= i < ps.len() ==> is_map(#[trigger] ps[i].act),
    ensures cfold(c, ps, k, be, af) == Some(match lnc(ps, k) {
        None => c, Some(Act::PutBytes(b)) => Cache::Bytes(b), Some(_) => Cache::Missing })
    decreases ps.len()
{
    if ps.len() > 0 {
        let q = ps.drop_last();
        assert forall|i: int| 0 <= i < q.len() implies is_map(#[trigger] q[i].act) by { assert(q[i] == ps[i]); }
        assert(is_map(ps[ps.len() - 1].act));
        lemma_other_maps(c, q, k, be, af);
    }
}

proof fn lemma_texts(c: Cache, ps: Seq<P>, k: int, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires forall|i: int| 0 <= i < ps.len() ==> (#[trigger] ps[i].act) is Ed,
    ensures
        edits_of(ps, k).len() == 0 ==> cfold(c, ps, k, be, af) == Some(c),
        c is Str ==> cfold(c, ps, k, be, af) == match fold(c->Str_0, edits_of(ps, k)) {
            Some(t) => Some(Cache::Str(t)), None => None },
    decreases ps.len()
{
    if ps.len() > 0 {
        let q = ps.drop_last();
        assert forall|i: int| 0 <= i < q.len() implies (#[trigger] q[i].act) is Ed by { assert(q[i] == ps[i]); }
        assert(ps[ps.len() - 1].act is Ed);
        lemma_texts(c, q, k, be, af);
        if ps.last().key == k { assert(edits_of(ps, k).drop_last() =~= edits_of(q, k)); }
    }
}

// THEOREM (cache): starting from cache == doc before, the cache after the message equals the
// doc after it at every key, and no `expect` panics.
proof fn theorem_cache(ps: Seq<P>, m: int, k: int, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires am_contract(ps, m, k, be, af),
    ensures cfold(cache_of(be(k)), ps, k, be, af) == Some(cache_of(af(k))),
{
    let maps = ps.subrange(0, m);
    let texts = ps.subrange(m, ps.len() as int);
    assert(ps =~= maps + texts);
    lemma_append(cache_of(be(k)), maps, texts, k, be, af);
    assert forall|i: int| 0 <= i < maps.len() implies is_map(#[trigger] maps[i].act) by { assert(maps[i] == ps[i]); }
    assert forall|i: int| 0 <= i < texts.len() implies (#[trigger] texts[i].act) is Ed by { assert(texts[i] == ps[m + i]); }
    if af(k) is Text {
        assert forall|i: int| 0 <= i < maps.len() && #[trigger] maps[i].key == k implies
            !(maps[i].act is PutBytes) && !(maps[i].act is PutOther) by { assert(maps[i] == ps[i]); assert(ps[i].key == k); }
        lemma_text_maps(cache_of(be(k)), maps, k, be, af);
        if exists|i: int| 0 <= i < m && #[trigger] resets(ps[i], k, be, af) {
            let i = choose|i: int| 0 <= i < m && #[trigger] resets(ps[i], k, be, af);
            assert(maps[i] == ps[i]); assert(resets(maps[i], k, be, af));
            lemma_texts(Cache::Str(seq![]), texts, k, be, af);
        } else {
            assert forall|i: int| 0 <= i < maps.len() implies !#[trigger] resets(maps[i], k, be, af) by {
                assert(maps[i] == ps[i]); assert(!resets(ps[i], k, be, af)); }
            lemma_texts(cache_of(be(k)), texts, k, be, af);
        }
    } else {
        lemma_other_maps(cache_of(be(k)), maps, k, be, af);
        let mid = cfold(cache_of(be(k)), maps, k, be, af).unwrap();
        lemma_texts(mid, texts, k, be, af);
    }
}

// Daemon editor path (file open in an editor, before(k) is Text(_, tb), the editor holds tb).
// FileRemoval: file_deltas.retain(other files) then push delete(|content before|);
// FileChange: push. Bytes are not sent to editors (out of scope: contract forbids for k).
pub enum D { DelAll(nat), E(Edit) }

pub open spec fn dstep(ds: Seq<D>, p: P, k: int, tb: Seq<char>) -> Seq<D> {
    if p.key != k { ds } else {
        match p.act {
            Act::PutText(_) | Act::PutOther | Act::DelMap => ds.push(D::DelAll(tb.len())),
            Act::Ed(e) => ds.push(D::E(e)),
            _ => ds,
        }
    }
}

pub open spec fn dfold(ps: Seq<P>, k: int, tb: Seq<char>, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    -> Seq<D> decreases ps.len() {
    if ps.len() == 0 { seq![] } else { dstep(dfold(ps.drop_last(), k, tb, be, af), convert(ps.last(), be, af), k, tb) }
}

pub open spec fn eapply(s: Seq<char>, d: D) -> Option<Seq<char>> {
    match d { D::DelAll(n) => apply(s, Edit::Del(0, n)), D::E(e) => apply(s, e) }
}

pub open spec fn efold(s: Seq<char>, ds: Seq<D>) -> Option<Seq<char>> decreases ds.len() {
    if ds.len() == 0 { Some(s) } else {
        match efold(s, ds.drop_last()) { Some(t) => eapply(t, ds.last()), None => None }
    }
}

proof fn lemma_dmaps(ps: Seq<P>, k: int, tb: Seq<char>, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires forall|i: int| 0 <= i < ps.len() ==> is_map(#[trigger] ps[i].act),
        !(af(k) is Bytes),
    ensures dfold(ps, k, tb, be, af) == if exists|i: int| 0 <= i < ps.len() && #[trigger] resets(ps[i], k, be, af)
        { seq![D::DelAll(tb.len())] } else { Seq::<D>::empty() }
    decreases ps.len()
{
    if ps.len() > 0 {
        let q = ps.drop_last();
        let l = ps.len() - 1;
        assert(ps.last() == ps[l]);
        assert forall|i: int| 0 <= i < q.len() implies is_map(#[trigger] q[i].act) by { assert(q[i] == ps[i]); }
        lemma_dmaps(q, k, tb, be, af);
        assert(is_map(ps[l].act));
        let cl = convert(ps[l], be, af);
        if resets(ps[l], k, be, af) {
            assert(cl.key == k && (cl.act is PutText || cl.act is DelMap || cl.act is PutOther));
        } else {
            assert(dstep(dfold(q, k, tb, be, af), cl, k, tb) == dfold(q, k, tb, be, af));
        }
        if exists|i: int| 0 <= i < ps.len() && #[trigger] resets(ps[i], k, be, af) {
            if !resets(ps[l], k, be, af) {
                let i = choose|i: int| 0 <= i < ps.len() && #[trigger] resets(ps[i], k, be, af);
                assert(q[i] == ps[i]); assert(resets(q[i], k, be, af));
            }
        } else {
            assert forall|i: int| 0 <= i < q.len() implies !#[trigger] resets(q[i], k, be, af) by {
                assert(q[i] == ps[i]); assert(!resets(ps[i], k, be, af)); }
        }
    }
}

pub open spec fn emap(es: Seq<Edit>) -> Seq<D> { es.map_values(|e: Edit| D::E(e)) }

proof fn lemma_dtexts(pre: Seq<D>, ps: Seq<P>, k: int, tb: Seq<char>, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires forall|i: int| 0 <= i < ps.len() ==> (#[trigger] ps[i].act) is Ed,
    ensures dfold_from(pre, ps, k, tb, be, af) == pre + emap(edits_of(ps, k))
    decreases ps.len()
{
    if ps.len() > 0 {
        let q = ps.drop_last();
        assert forall|i: int| 0 <= i < q.len() implies (#[trigger] q[i].act) is Ed by { assert(q[i] == ps[i]); }
        assert(ps[ps.len() - 1].act is Ed);
        lemma_dtexts(pre, q, k, tb, be, af);
        assert(pre + emap(edits_of(ps, k)) =~= if ps.last().key == k {
            (pre + emap(edits_of(q, k))).push(D::E(ps.last().act->Ed_0)) } else { pre + emap(edits_of(q, k)) });
    }
}

pub open spec fn dfold_from(pre: Seq<D>, ps: Seq<P>, k: int, tb: Seq<char>, be: spec_fn(int) -> Val,
    af: spec_fn(int) -> Val) -> Seq<D> decreases ps.len() {
    if ps.len() == 0 { pre } else { dstep(dfold_from(pre, ps.drop_last(), k, tb, be, af), convert(ps.last(), be, af), k, tb) }
}

proof fn lemma_dfold_append(a: Seq<P>, b: Seq<P>, k: int, tb: Seq<char>, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    ensures dfold(a + b, k, tb, be, af) == dfold_from(dfold(a, k, tb, be, af), b, k, tb, be, af)
    decreases b.len()
{
    if b.len() == 0 { assert(a + b =~= a); } else {
        lemma_dfold_append(a, b.drop_last(), k, tb, be, af);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

proof fn lemma_efold_e(s: Seq<char>, es: Seq<Edit>)
    ensures efold(s, emap(es)) == fold(s, es)
    decreases es.len()
{
    if es.len() > 0 {
        lemma_efold_e(s, es.drop_last());
        assert(emap(es).drop_last() =~= emap(es.drop_last()));
    }
}

proof fn lemma_efold_delall(tb: Seq<char>, es: Seq<Edit>)
    ensures efold(tb, seq![D::DelAll(tb.len())] + emap(es)) == fold(seq![], es)
    decreases es.len()
{
    let x = seq![D::DelAll(tb.len())];
    if es.len() == 0 {
        assert(x + emap(es) =~= x);
        assert(x.drop_last() =~= Seq::<D>::empty());
        assert(tb.subrange(0, 0) + tb.subrange(tb.len() as int, tb.len() as int) =~= Seq::<char>::empty());
        assert(x.last() == D::DelAll(tb.len()));
        assert(efold(tb, x.drop_last()) == Some(tb));
        assert(eapply(tb, D::DelAll(tb.len())) == Some(Seq::<char>::empty()));
        assert(efold(tb, x) == Some(Seq::<char>::empty()));
        assert(fold(Seq::<char>::empty(), es) == Some(Seq::<char>::empty()));
    } else {
        lemma_efold_delall(tb, es.drop_last());
        let y = x + emap(es);
        assert(y.drop_last() =~= x + emap(es.drop_last()));
        assert(y.last() == D::E(es.last()));
        assert(efold(tb, y) == match efold(tb, y.drop_last()) { Some(t) => eapply(t, y.last()), None => None });
    }
}

// THEOREM (editor): the editor, holding the doc's text before the message, ends at the doc's
// text after it ("" if the file was deleted: the daemon then re-creates it empty).
proof fn theorem_editor(ps: Seq<P>, m: int, k: int, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires am_contract(ps, m, k, be, af), be(k) is Text, !(af(k) is Bytes),
    ensures efold(be(k)->Text_1, dfold(ps, k, be(k)->Text_1, be, af))
        == Some(match af(k) { Val::Text(_, t) => t, _ => Seq::<char>::empty() }),
{
    let tb = be(k)->Text_1;
    let maps = ps.subrange(0, m);
    let texts = ps.subrange(m, ps.len() as int);
    assert(ps =~= maps + texts);
    assert forall|i: int| 0 <= i < maps.len() implies is_map(#[trigger] maps[i].act) by { assert(maps[i] == ps[i]); }
    assert forall|i: int| 0 <= i < texts.len() implies (#[trigger] texts[i].act) is Ed by { assert(texts[i] == ps[m + i]); }
    lemma_dfold_append(maps, texts, k, tb, be, af);
    lemma_dmaps(maps, k, tb, be, af);
    let pre = dfold(maps, k, tb, be, af);
    lemma_dtexts(pre, texts, k, tb, be, af);
    let es = edits_of(texts, k);
    let has = exists|i: int| 0 <= i < maps.len() && #[trigger] resets(maps[i], k, be, af);
    let hasp = exists|i: int| 0 <= i < m && #[trigger] resets(ps[i], k, be, af);
    assert(has == hasp) by {
        if has { let i = choose|i: int| 0 <= i < maps.len() && #[trigger] resets(maps[i], k, be, af);
            assert(maps[i] == ps[i]); assert(resets(ps[i], k, be, af)); }
        if hasp { let i = choose|i: int| 0 <= i < m && #[trigger] resets(ps[i], k, be, af);
            assert(maps[i] == ps[i]); assert(resets(maps[i], k, be, af)); }
    }
    if has { lemma_efold_delall(tb, es); } else {
        assert(pre + emap(es) =~= emap(es));
        lemma_efold_e(tb, es);
        if af(k) is Absent {
            // Absent and no reset: lnc must be None (DelMap/PutText/PutOther reset), so before Absent: contradiction.
            lemma_lnc_reset(maps, k, be, af);
        }
    }
}

proof fn lemma_lnc_reset(ps: Seq<P>, k: int, be: spec_fn(int) -> Val, af: spec_fn(int) -> Val)
    requires !(af(k) is Text), forall|i: int| 0 <= i < ps.len() ==> is_map(#[trigger] ps[i].act),
    ensures (lnc(ps, k) is Some && !(lnc(ps, k)->Some_0 is PutBytes)) ==>
        exists|i: int| 0 <= i < ps.len() && #[trigger] resets(ps[i], k, be, af)
    decreases ps.len()
{
    if ps.len() > 0 {
        let q = ps.drop_last();
        let l = ps.len() - 1;
        assert(ps.last() == ps[l]);
        assert(is_map(ps[l].act));
        assert forall|i: int| 0 <= i < q.len() implies is_map(#[trigger] q[i].act) by { assert(q[i] == ps[i]); }
        lemma_lnc_reset(q, k, be, af);
        if lnc(ps, k) is Some && !(lnc(ps, k)->Some_0 is PutBytes) {
            if ps[l].key == k && !(ps[l].act is Conflict) { assert(resets(ps[l], k, be, af)); } else {
                let i = choose|i: int| 0 <= i < q.len() && #[trigger] resets(q[i], k, be, af);
                assert(q[i] == ps[i]); assert(resets(ps[i], k, be, af));
            }
        }
    }
}

// Non-vacuity: a concrete message where the visible object is switched by a Conflict only
// (the case replaced_text_objects_as_puts exists for) satisfies the contract.
proof fn example_conflict_switch() {
    let be = |k: int| if k == 0 { Val::Text(1, seq!['o']) } else { Val::Absent };
    let af = |k: int| if k == 0 { Val::Text(2, seq!['n']) } else { Val::Absent };
    let ps = seq![P { key: 0, act: Act::Conflict }, P { key: 0, act: Act::Ed(Edit::Splice(0, seq!['n'])) }];
    assert(resets(ps[0], 0, be, af));
    let t = ps.subrange(1, 2);
    assert(t.drop_last() =~= Seq::<P>::empty());
    assert(edits_of(t.drop_last(), 0) =~= Seq::<Edit>::empty());
    assert(t.last() == ps[1]);
    assert(edits_of(t, 0) =~= seq![Edit::Splice(0, seq!['n'])]);
    assert(ps[0].act is Conflict && ps[1].act is Ed);
    assert(forall|i: int| 0 <= i < 1 ==> is_map(#[trigger] ps[i].act));
    assert(forall|i: int| 1 <= i < 2 ==> (#[trigger] ps[i].act) is Ed);
    assert(seq![Edit::Splice(0, seq!['n'])].drop_last() =~= Seq::<Edit>::empty());
    assert(Seq::<char>::empty().subrange(0, 0) + seq!['n'] + Seq::<char>::empty().subrange(0, 0) =~= seq!['n']);
    let es = edits_of(t, 0);
    assert(es.drop_last() =~= Seq::<Edit>::empty());
    assert(es.last() == Edit::Splice(0, seq!['n']));
    assert(fold(Seq::<char>::empty(), es.drop_last()) == Some(Seq::<char>::empty()));
    assert(apply(Seq::<char>::empty(), Edit::Splice(0, seq!['n'])) == Some(seq!['n']));
    assert(fold(Seq::<char>::empty(), es) == Some(seq!['n']));
    assert(exists|i: int| 0 <= i < 1 && #[trigger] resets(ps[i], 0, be, af));
    assert(forall|i: int| 0 <= i < 1 && #[trigger] ps[i].key == 0 ==>
        !(ps[i].act is PutBytes) && !(ps[i].act is PutOther));
    assert(am_contract(ps, 1, 0, be, af));
    theorem_cache(ps, 1, 0, be, af);
    theorem_editor(ps, 1, 0, be, af);
}

fn main() {}
}
