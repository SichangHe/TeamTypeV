// (authored by agents) Verus model of document.rs cache maintenance (receive_sync_message_log_patches)
use vstd::prelude::*;
verus! {

pub type Path = nat;
pub enum Entry { Text(Seq<int>), Bytes(Seq<int>) }
pub type View = Map<Path, Entry>;

pub open spec fn get(m: View, p: Path) -> Option<Entry> {
    if m.dom().contains(p) { Some(m[p]) } else { None }
}
pub open spec fn is_txt(m: View, p: Path) -> bool {
    m.dom().contains(p) && m[p] is Text
}
/// text of p, "" if p is absent or bytes (what the cache code does for FileChange on a missing/bytes entry)
pub open spec fn txt(m: View, p: Path) -> Seq<int> {
    if is_txt(m, p) { m[p]->Text_0 } else { Seq::empty() }
}
pub open spec fn rep(t: Seq<int>, i: int, n: int, s: Seq<int>) -> Seq<int> {
    t.subrange(0, i) + s + t.subrange(i + n, t.len() as int)
}
pub open spec fn rep_ok(t: Seq<int>, i: int, n: int) -> bool {
    0 <= i && 0 <= n && i + n <= t.len()
}

/// Abstract Automerge patch, already in the shape types.rs accepts
/// (PutText = PutMap(Text) incl. the replaced_text_objects_as_puts rewrite; Conflict = Conflict).
pub enum Patch {
    PutText(Path),
    PutBytes(Path, Seq<int>),
    Delete(Path),
    Splice(Path, int, Seq<int>),
    DelSeq(Path, int, int),
    Conflict(Path),
}

/// ASSUMED semantics of a patch (Automerge patch log replayed on the previous visible state).
pub open spec fn step_view(v: View, pt: Patch) -> Option<View> {
    match pt {
        Patch::PutText(p) => Some(v.insert(p, Entry::Text(Seq::empty()))),
        Patch::PutBytes(p, b) => Some(v.insert(p, Entry::Bytes(b))),
        Patch::Delete(p) => Some(v.remove(p)),
        Patch::Splice(p, i, s) =>
            if is_txt(v, p) && rep_ok(txt(v, p), i, 0) {
                Some(v.insert(p, Entry::Text(rep(txt(v, p), i, 0, s))))
            } else { None },
        Patch::DelSeq(p, i, n) =>
            if is_txt(v, p) && rep_ok(txt(v, p), i, n) {
                Some(v.insert(p, Entry::Text(rep(txt(v, p), i, n, Seq::empty()))))
            } else { None },
        Patch::Conflict(_) => Some(v),
    }
}

pub open spec fn replay(v: View, ps: Seq<Patch>) -> Option<View>
    decreases ps.len(),
{
    if ps.len() == 0 { Some(v) } else {
        match step_view(v, ps[0]) {
            Some(v1) => replay(v1, ps.drop_first()),
            None => None,
        }
    }
}

/// Cache update performed by the Rust code for one effect; `f` is the document AFTER the whole
/// message (the code consults text_obj(path) on the final document for FileRemoval).
pub open spec fn gfin(f: View, p: Path) -> Option<Entry> {
    if is_txt(f, p) { Some(Entry::Text(Seq::empty())) } else { None }
}
pub open spec fn cache_set(c: View, p: Path, o: Option<Entry>) -> View {
    match o { Some(e) => c.insert(p, e), None => c.remove(p) }
}
pub open spec fn cache_step(c: View, f: View, pt: Patch) -> View {
    match pt {
        Patch::PutText(p) => cache_set(c, p, gfin(f, p)),
        Patch::Delete(p) => cache_set(c, p, gfin(f, p)),
        Patch::PutBytes(p, b) => c.insert(p, Entry::Bytes(b)),
        Patch::Splice(p, i, s) => c.insert(p, Entry::Text(rep(txt(c, p), i, 0, s))),
        Patch::DelSeq(p, i, n) => c.insert(p, Entry::Text(rep(txt(c, p), i, n, Seq::empty()))),
        Patch::Conflict(_) => c,
    }
}
/// The delta applied to the cache text must fit (else the Rust code panics).
pub open spec fn cache_fits(c: View, pt: Patch) -> bool {
    match pt {
        Patch::Splice(p, i, _) => rep_ok(txt(c, p), i, 0),
        Patch::DelSeq(p, i, n) => rep_ok(txt(c, p), i, n),
        _ => true,
    }
}

pub open spec fn rel_at(c: View, v: View, f: View, p: Path) -> bool {
    get(c, p) == get(v, p)
    || (get(c, p) == gfin(f, p)
        && (get(v, p) is None || get(v, p) == Some(Entry::Text(Seq::<int>::empty()))))
}
pub open spec fn rel(c: View, v: View, f: View) -> bool {
    forall|p: Path| #[trigger] rel_at(c, v, f, p)
}

pub proof fn step_preserves(c: View, v: View, f: View, pt: Patch)
    requires rel(c, v, f), step_view(v, pt) is Some,
    ensures
        cache_fits(c, pt),
        rel(cache_step(c, f, pt), step_view(v, pt)->Some_0, f),
{
    let v1 = step_view(v, pt)->Some_0;
    let c1 = cache_step(c, f, pt);
    // the text of c at the touched path equals that of v (both absent/empty or equal)
    match pt {
        Patch::Splice(p, _, _) | Patch::DelSeq(p, _, _) => {
            assert(rel_at(c, v, f, p));
            assert(txt(c, p) == txt(v, p));
        }
        _ => {}
    }
    assert forall|q: Path| #[trigger] rel_at(c1, v1, f, q) by {
        assert(rel_at(c, v, f, q));
        match pt {
            Patch::PutText(p) | Patch::Delete(p) => {
                if q == p {
                    if is_txt(f, p) { assert(get(c1, q) == get(v1, q) || true); }
                }
            }
            Patch::Splice(p, i, s) => {
                if q == p { assert(get(c1, q) == get(v1, q)); }
            }
            Patch::DelSeq(p, i, n) => {
                if q == p { assert(get(c1, q) == get(v1, q)); }
            }
            _ => {}
        }
    }
}

/// Final theorem: if the cache starts equal to the document, then after the cache is updated with
/// every effect of a message whose patches replay to f, the cache equals f.
pub proof fn replay_preserves(c: View, v: View, f: View, ps: Seq<Patch>)
    requires rel(c, v, f), replay(v, ps) == Some(f),
    ensures forall|p: Path| #[trigger] get(fold_cache(c, f, ps), p) == get(f, p),
    decreases ps.len(),
{
    if ps.len() == 0 {
        assert forall|p: Path| #[trigger] get(c, p) == get(f, p) by {
            assert(rel_at(c, f, f, p));
        }
    } else {
        let v1 = step_view(v, ps[0])->Some_0;
        step_preserves(c, v, f, ps[0]);
        replay_preserves(cache_step(c, f, ps[0]), v1, f, ps.drop_first());
    }
}

pub open spec fn fold_cache(c: View, f: View, ps: Seq<Patch>) -> View
    decreases ps.len(),
{
    if ps.len() == 0 { c } else { fold_cache(cache_step(c, f, ps[0]), f, ps.drop_first()) }
}

// ======================= daemon.rs: ReceiveSyncMessage handling =======================

pub struct Rep { pub i: int, pub n: int, pub s: Seq<int> }
pub open spec fn app(t: Seq<int>, r: Rep) -> Seq<int> { rep(t, r.i, r.n, r.s) }
pub open spec fn app_all(t: Seq<int>, ds: Seq<Rep>) -> Seq<int>
    decreases ds.len(),
{
    if ds.len() == 0 { t } else { app(app_all(t, ds.drop_last()), ds.last()) }
}
pub open spec fn app_ok(t: Seq<int>, ds: Seq<Rep>) -> bool
    decreases ds.len(),
{
    if ds.len() == 0 { true } else {
        app_ok(t, ds.drop_last())
            && rep_ok(app_all(t, ds.drop_last()), ds.last().i, ds.last().n)
    }
}
proof fn app_push(t: Seq<int>, ds: Seq<Rep>, r: Rep)
    ensures
        app_all(t, ds.push(r)) == app(app_all(t, ds), r),
        app_ok(t, ds.push(r)) == (app_ok(t, ds) && rep_ok(app_all(t, ds), r.i, r.n)),
{
    assert(ds.push(r).drop_last() =~= ds);
}

/// Daemon state touched while handling one ReceiveSyncMessage.
/// `own` holds (editor, path) pairs: the editor has the file open (OTServer present).
pub struct D {
    pub cache: View,           // Document.files == the CRDT (revival keeps them equal)
    pub view: View,            // ghost: CRDT state after the patches processed so far
    pub own: Set<(nat, nat)>,
    pub deltas: Map<Path, Seq<Rep>>, // file_deltas, grouped per path (editors treat paths independently)
    pub disk: View,
    pub pend: Set<Path>,       // paths in file_deltas (written after the loop)
    pub done: Set<Path>,       // ghost: paths touched so far
}

/// Constants of one message: excluded paths, buffers at the start, CRDT before and after.
pub struct K { pub excl: spec_fn(Path) -> bool, pub buf0: Map<(nat, nat), Seq<int>>, pub c0: View, pub f: View }

pub open spec fn owned_any(own: Set<(nat, nat)>, p: Path) -> bool {
    exists|e: nat| #[trigger] own.contains((e, p))
}
pub open spec fn inval(own: Set<(nat, nat)>, p: Path) -> Set<(nat, nat)> {
    own.filter(|k: (nat, nat)| k.1 != p)
}
pub open spec fn dl(d: D, p: Path) -> Seq<Rep> {
    if d.deltas.dom().contains(p) { d.deltas[p] } else { Seq::empty() }
}
/// write_file when git is not running: writes the cache text/bytes, does nothing if the cache lacks the path.
pub open spec fn wr(disk: View, cache: View, p: Path) -> View {
    if cache.dom().contains(p) { disk.insert(p, cache[p]) } else { disk }
}

/// One effect of the `for patch_effect in patch_effects` loop in daemon.rs (git not running).
pub open spec fn dstep(k: K, d: D, pt: Patch) -> D {
    let v1 = step_view(d.view, pt)->Some_0;
    match pt {
        Patch::Splice(p, i, s) => D {
            view: v1,
            deltas: d.deltas.insert(p, dl(d, p).push(Rep { i, n: 0, s })),
            pend: d.pend.insert(p), done: d.done.insert(p), ..d },
        Patch::DelSeq(p, i, n) => D {
            view: v1,
            deltas: d.deltas.insert(p, dl(d, p).push(Rep { i, n, s: Seq::empty() })),
            pend: d.pend.insert(p), done: d.done.insert(p), ..d },
        Patch::PutBytes(p, _) => D {
            view: v1,
            disk: if (k.excl)(p) { d.disk } else { wr(d.disk, d.cache, p) },
            done: d.done.insert(p), ..d },
        Patch::Conflict(_) => D { view: v1, ..d },
        Patch::PutText(p) | Patch::Delete(p) =>
            if (k.excl)(p) { D { view: v1, done: d.done.insert(p), ..d } }
            else if !owned_any(d.own, p) {
                if d.cache.dom().contains(p) {
                    D { view: v1, disk: wr(d.disk, d.cache, p), done: d.done.insert(p), ..d }
                } else {
                    D { view: v1, disk: d.disk.remove(p), done: d.done.insert(p), ..d }
                }
            } else {
                // editor owns it: replace earlier deltas by "delete all previous content", bring back empty file
                let before = txt(k.c0, p).len() as int;
                D { view: v1,
                    deltas: d.deltas.insert(p, seq![Rep { i: 0, n: before, s: Seq::empty() }]),
                    cache: if d.cache.dom().contains(p) { d.cache }
                           else { d.cache.insert(p, Entry::Text(Seq::empty())) },
                    pend: d.pend.insert(p), done: d.done.insert(p), ..d }
            },
    }
}

pub open spec fn fin_dom(k: K, d: D) -> Set<Path> {
    d.disk.dom().union(d.pend.intersect(d.cache.dom()).filter(|p: Path| !(k.excl)(p)))
}
pub open spec fn fin_write(k: K, d: D) -> View {
    Map::new(
        fin_dom(k, d),
        |p: Path| if d.pend.contains(p) && d.cache.dom().contains(p) && !(k.excl)(p) { d.cache[p] }
                  else { d.disk[p] },
    )
}

pub open spec fn inv_cache(k: K, d: D) -> bool {
    forall|p: Path| #![trigger get(d.cache, p)]
        get(d.cache, p) == get(k.f, p)
        || (get(k.f, p) is None && get(d.cache, p) == Some(Entry::Text(Seq::<int>::empty())))
}
pub open spec fn inv_buf(k: K, d: D) -> bool {
    forall|e: nat, p: Path| #[trigger] d.own.contains((e, p)) ==> {
        &&& k.buf0.dom().contains((e, p))
        &&& is_txt(k.c0, p) && k.buf0[(e, p)] == txt(k.c0, p)
        &&& !(k.excl)(p)
        &&& app_ok(k.buf0[(e, p)], dl(d, p))
        &&& app_all(k.buf0[(e, p)], dl(d, p)) == txt(d.view, p)
    }
}
pub open spec fn inv_m(k: K, d: D) -> bool {
    forall|p: Path| #[trigger] owned_any(d.own, p) ==> {
        &&& (is_txt(d.view, p) || get(d.view, p) is None)
        &&& (get(d.view, p) is None ==>
                get(d.cache, p) == Some(Entry::Text(Seq::<int>::empty())) || get(k.f, p) is Some)
    }
}
pub open spec fn inv_disk(k: K, d: D) -> bool {
    forall|p: Path| #![trigger get(d.disk, p)]
        (!owned_any(d.own, p) && !(k.excl)(p)) ==> {
            if !d.done.contains(p) {
                get(d.disk, p) == get(k.c0, p)
            } else {
                get(d.disk, p) == get(d.cache, p)
                || (d.pend.contains(p) && d.cache.dom().contains(p))
                || (!d.cache.dom().contains(p) && get(d.view, p) is Some)
            }
        }
}
pub open spec fn inv_misc(k: K, d: D) -> bool {
    &&& forall|p: Path| #![trigger get(d.view, p)] !d.done.contains(p) ==> get(d.view, p) == get(k.c0, p)
    &&& forall|p: Path| #![trigger get(d.cache, p)] get(d.cache, p) != get(k.f, p) ==> d.done.contains(p)
    &&& forall|p: Path| #[trigger] d.pend.contains(p) ==> d.done.contains(p)
}
pub open spec fn inv(k: K, d: D) -> bool {
    inv_cache(k, d) && inv_buf(k, d) && inv_m(k, d) && inv_disk(k, d) && inv_misc(k, d)
}

pub open spec fn tpath(pt: Patch) -> Path {
    match pt {
        Patch::Splice(p, _, _) | Patch::DelSeq(p, _, _) | Patch::PutBytes(p, _)
        | Patch::PutText(p) | Patch::Delete(p) | Patch::Conflict(p) => p,
    }
}
proof fn dstep_done(k: K, d: D, pt: Patch)
    requires step_view(d.view, pt) is Some,
    ensures
        dstep(k, d, pt).done == (if pt is Conflict { d.done } else { d.done.insert(tpath(pt)) }),
        dstep(k, d, pt).view == step_view(d.view, pt)->Some_0,
{
    match pt {
        Patch::PutText(p) | Patch::Delete(p) => {
            if (k.excl)(p) {} else if !owned_any(d.own, p) {
                if d.cache.dom().contains(p) {} else {}
            } else {}
        }
        _ => {}
    }
}

proof fn fin_get(k: K, d: D, p: Path)
    ensures get(fin_write(k, d), p) ==
        (if d.pend.contains(p) && d.cache.dom().contains(p) && !(k.excl)(p) { Some(d.cache[p]) }
         else { get(d.disk, p) }),
{
    let fw = fin_write(k, d);
    if d.pend.contains(p) && d.cache.dom().contains(p) && !(k.excl)(p) {
        assert(fin_dom(k, d).contains(p));
    } else {
        assert(fin_dom(k, d).contains(p) == d.disk.dom().contains(p));
    }
}

proof fn inval_props(own: Set<(nat, nat)>, p: Path)
    ensures
        forall|e: nat, q: Path| #[trigger] inval(own, p).contains((e, q)) <==> (own.contains((e, q)) && q != p),
        forall|q: Path| #[trigger] owned_any(inval(own, p), q) <==> (q != p && owned_any(own, q)),
{
    assert forall|q: Path| #[trigger] owned_any(inval(own, p), q) <==> (q != p && owned_any(own, q)) by {
        if owned_any(inval(own, p), q) {
            let e = choose|e: nat| inval(own, p).contains((e, q));
            assert(own.contains((e, q)));
        }
        if q != p && owned_any(own, q) {
            let e = choose|e: nat| own.contains((e, q));
            assert(inval(own, p).contains((e, q)));
        }
    }
}

pub proof fn dstep_preserves(k: K, d: D, pt: Patch)
    requires inv(k, d), step_view(d.view, pt) is Some,
    ensures inv_cache(k, dstep(k, d, pt)), inv_buf(k, dstep(k, d, pt)), inv_m(k, dstep(k, d, pt)), inv_disk(k, dstep(k, d, pt)), inv_misc(k, dstep(k, d, pt)),
{
    let d1 = dstep(k, d, pt);
    dstep_done(k, d, pt);
    inval_props(d.own, match pt { Patch::PutBytes(p, _) => p, _ => 0 });
    match pt {
        Patch::Splice(p, i, s) => {
            let r = Rep { i, n: 0, s };
            assert forall|e: nat, q: Path| #[trigger] d1.own.contains((e, q)) implies {
                &&& k.buf0.dom().contains((e, q))
                &&& is_txt(k.c0, q) && k.buf0[(e, q)] == txt(k.c0, q)
                &&& !(k.excl)(q)
                &&& app_ok(k.buf0[(e, q)], dl(d1, q))
                &&& app_all(k.buf0[(e, q)], dl(d1, q)) == txt(d1.view, q)
            } by {
                if q == p { app_push(k.buf0[(e, q)], dl(d, p), r); }
            }
        }
        Patch::DelSeq(p, i, n) => {
            let r = Rep { i, n, s: Seq::empty() };
            assert forall|e: nat, q: Path| #[trigger] d1.own.contains((e, q)) implies {
                &&& k.buf0.dom().contains((e, q))
                &&& is_txt(k.c0, q) && k.buf0[(e, q)] == txt(k.c0, q)
                &&& !(k.excl)(q)
                &&& app_ok(k.buf0[(e, q)], dl(d1, q))
                &&& app_all(k.buf0[(e, q)], dl(d1, q)) == txt(d1.view, q)
            } by {
                if q == p { app_push(k.buf0[(e, q)], dl(d, p), r); }
            }
        }
        Patch::PutText(p) | Patch::Delete(p) => {
            if !(k.excl)(p) && owned_any(d.own, p) {
                let e = choose|e: nat| d.own.contains((e, p));
                assert(k.buf0[(e, p)] == txt(k.c0, p));
                let before = txt(k.c0, p).len() as int;
                let r = Rep { i: 0, n: before, s: Seq::empty() };
                let ds = seq![r];
                assert(ds.drop_last() =~= Seq::<Rep>::empty());
                assert(ds.last() == r);
                assert(app_all(k.buf0[(e, p)], Seq::<Rep>::empty()) == k.buf0[(e, p)]);
                assert(app_ok(k.buf0[(e, p)], Seq::<Rep>::empty()));
                assert(app_ok(k.buf0[(e, p)], ds));
                assert(app_all(k.buf0[(e, p)], ds) =~= Seq::<int>::empty());
                assert(txt(k.c0, p).subrange(0, 0) + Seq::<int>::empty() + txt(k.c0, p).subrange(before, before) =~= Seq::<int>::empty());
            }
        }
        _ => {}
    }
    assert forall|q: Path| #![trigger get(d1.cache, q)]
        get(d1.cache, q) == get(k.f, q)
        || (get(k.f, q) is None && get(d1.cache, q) == Some(Entry::Text(Seq::<int>::empty()))) by {
        assert(get(d.cache, q) == get(k.f, q)
            || (get(k.f, q) is None && get(d.cache, q) == Some(Entry::Text(Seq::<int>::empty()))));
    }
    assert forall|q: Path| #![trigger get(d1.view, q)] !d1.done.contains(q) implies get(d1.view, q) == get(k.c0, q) by {
        assert(!d.done.contains(q));
        if !(pt is Conflict) { assert(q != tpath(pt)); }
        assert(get(step_view(d.view, pt)->Some_0, q) == get(d.view, q));
    }
    assert forall|q: Path| #![trigger get(d1.cache, q)] get(d1.cache, q) != get(k.f, q) implies d1.done.contains(q) by {
        if !d.done.contains(q) { assert(get(d.cache, q) == get(k.f, q)); }
    }
    assert forall|q: Path| #[trigger] d1.pend.contains(q) implies d1.done.contains(q) by {
        if d.pend.contains(q) { assert(d.done.contains(q)); }
    }
}

pub open spec fn fold_d(k: K, d: D, ps: Seq<Patch>) -> D
    decreases ps.len(),
{
    if ps.len() == 0 { d } else {
        fold_d(k, dstep(k, d, ps[0]), ps.drop_first())
    }
}

/// State right after Document::receive_sync_message_log_patches: cache == f.
pub open spec fn init_d(k: K, own0: Set<(nat, nat)>, disk0: View) -> D {
    D { cache: k.f, view: k.c0, own: own0, deltas: Map::empty(), disk: disk0,
        pend: Set::empty(), done: Set::empty() }
}
/// Assumptions on the state before the message (invariants of the daemon between messages).
pub open spec fn pre(k: K, own0: Set<(nat, nat)>, disk0: View) -> bool {
    // an editor that owns a file holds exactly the daemon's text (in-flight OT is the concurrency proof's job)
    &&& forall|e: nat, p: Path| #[trigger] own0.contains((e, p)) ==> {
        &&& k.buf0.dom().contains((e, p))
        &&& is_txt(k.c0, p) && k.buf0[(e, p)] == txt(k.c0, p)
        &&& !(k.excl)(p)
    }
    // disk equals cache for files no editor owns (excluded paths are never mirrored)
    &&& forall|p: Path| #![trigger get(disk0, p)]
        (!owned_any(own0, p) && !(k.excl)(p)) ==> get(disk0, p) == get(k.c0, p)
}

pub proof fn init_inv(k: K, own0: Set<(nat, nat)>, disk0: View)
    requires pre(k, own0, disk0),
    ensures inv(k, init_d(k, own0, disk0)),
{
    let d = init_d(k, own0, disk0);
    assert forall|e: nat, p: Path| #[trigger] d.own.contains((e, p)) implies app_ok(k.buf0[(e, p)], dl(d, p)) by {
        assert(dl(d, p) =~= Seq::<Rep>::empty());
    }
    assert forall|e: nat, p: Path| #[trigger] d.own.contains((e, p)) implies
        app_all(k.buf0[(e, p)], dl(d, p)) == txt(d.view, p) by {
        assert(dl(d, p) =~= Seq::<Rep>::empty());
    }
}

pub proof fn run(k: K, d: D, ps: Seq<Patch>)
    requires inv(k, d), replay(d.view, ps) == Some(k.f),
    ensures inv(k, fold_d(k, d, ps)), fold_d(k, d, ps).view == k.f,
    decreases ps.len(),
{
    if ps.len() > 0 {
        dstep_preserves(k, d, ps[0]);
        dstep_done(k, d, ps[0]);
        run(k, dstep(k, d, ps[0]), ps.drop_first());
    }
}

/// Main theorem for one ReceiveSyncMessage (git not running, writes succeed).
pub proof fn receive_sync_message_correct(
    k: K, own0: Set<(nat, nat)>, disk0: View, ps: Seq<Patch>,
)
    requires pre(k, own0, disk0), replay(k.c0, ps) == Some(k.f),
    ensures ({
        let dn = fold_d(k, init_d(k, own0, disk0), ps);
        // (1) cache = CRDT: equals the received document, plus empty files brought back for editors
        &&& (forall|p: Path| #![trigger get(dn.cache, p)]
                get(dn.cache, p) == get(k.f, p)
                || (get(k.f, p) is None
                    && get(dn.cache, p) == Some(Entry::Text(Seq::<int>::empty()))))
        // (2) every editor still owning a file: its buffer after the forwarded edits = cache text
        &&& (forall|e: nat, p: Path| #[trigger] dn.own.contains((e, p)) ==> {
                &&& is_txt(dn.cache, p)
                &&& app_ok(k.buf0[(e, p)], dl(dn, p))
                &&& app_all(k.buf0[(e, p)], dl(dn, p)) == txt(dn.cache, p)
            })
        // (3) after the writes, disk = cache for every non-excluded file no editor owns
        &&& (forall|p: Path| #![trigger get(fin_write(k, dn), p)]
                (!owned_any(dn.own, p) && !(k.excl)(p)) ==> get(fin_write(k, dn), p) == get(dn.cache, p))
    }),
{
    init_inv(k, own0, disk0);
    run(k, init_d(k, own0, disk0), ps);
    let dn = fold_d(k, init_d(k, own0, disk0), ps);
    assert forall|e: nat, p: Path| #[trigger] dn.own.contains((e, p)) implies {
        &&& is_txt(dn.cache, p)
        &&& app_ok(k.buf0[(e, p)], dl(dn, p))
        &&& app_all(k.buf0[(e, p)], dl(dn, p)) == txt(dn.cache, p)
    } by {
        assert(owned_any(dn.own, p));
    }
    let fw = fin_write(k, dn);
    assert forall|p: Path| #![trigger get(fw, p)]
        (!owned_any(dn.own, p) && !(k.excl)(p)) implies get(fw, p) == get(dn.cache, p) by {
        if !owned_any(dn.own, p) && !(k.excl)(p) {
            fin_get(k, dn, p);
            assert(get(dn.view, p) == get(k.f, p));
            if !dn.done.contains(p) {
                assert(get(dn.view, p) == get(k.c0, p));
                assert(get(dn.cache, p) == get(k.f, p));
                assert(!dn.pend.contains(p));
            } else if !(dn.pend.contains(p) && dn.cache.dom().contains(p)) {
                if !dn.cache.dom().contains(p) && get(dn.view, p) is Some {
                    assert(get(dn.cache, p) is None);
                }
            }
        }
    }
}

fn main() {}
}
