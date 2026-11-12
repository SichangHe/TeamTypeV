// (authored by agents) NEGATIVE CONTROL: reopen_without_barrier; Verus must reject it.
// (authored by agents) Verus model of the daemon's per-file editor ownership: many editors on one
// file, one CRDT text, handlers that run atomically (see DESIGN.md). Reuses conc.rs, a snapshot of
// ../concurrency/teamtype_concurrency.rs (one editor <-> one OTServer protocol, real ot.rs bodies).
use vstd::prelude::*;
#[path = "../../concurrency/teamtype_concurrency.rs"]
mod conc;
use conc::*;

verus! {

// CRDT content of the file `p` as the daemon's cache sees it. Other = absent or binary.
pub enum Ct { Text(Seq<char>), Other }

// State for one path. `eds` has an entry for exactly the editor connections whose
// `EditorConnection::ot_servers` contains the path (`EditorConnection::owns`).
pub struct M { pub ct: Ct, pub eds: Map<nat, W> }

pub open spec fn txt(m: M) -> Seq<char> { match m.ct { Ct::Text(t) => t, Ct::Other => Seq::empty() } }

// Every owner's OT server mirrors the CRDT text, and each owner's protocol state is the
// one-editor invariant of concurrency/. Owning needs a text CRDT file (so that the daemon's
// `apply_delta_to_doc(..).expect(..)` has a text to edit).
pub open spec fn inv_m(m: M) -> bool {
    forall|e: nat| m.eds.dom().contains(e) ==>
        m.ct is Text && inv(#[trigger] m.eds[e]) && m.eds[e].srv.cur == txt(m)
}

// ---------- CRDT-originated edits delivered to one editor, in order ----------
pub open spec fn steps(w: W, os: Seq<int>) -> W
    decreases os.len(),
{
    if os.len() == 0 { w } else { steps(crdt_step(w, os[0]), os.drop_first()) }
}

pub proof fn lemma_steps(w: W, os: Seq<int>)
    requires inv(w),
    ensures inv(steps(w, os)), steps(w, os).srv.cur == fold(w.srv.cur, os),
    decreases os.len(),
{
    if os.len() > 0 {
        lemma_crdt_step(w, os[0]);
        lemma_steps(crdt_step(w, os[0]), os.drop_first());
    }
}

// ---------- transitions: each is one atomic actor handler (or a piece of one) ----------

// `broadcast_to_editors(None, Edit)` for a CRDT change `os` (a sync message, a disk merge, a
// peer deleting a file an editor owns). The CRDT text moves by `os`, every owner's server gets
// the same ops in the same order.
pub open spec fn bcast(m: M, os: Seq<int>) -> M {
    M { ct: Ct::Text(fold(txt(m), os)),
        eds: Map::new(m.eds.dom(), |e: nat| steps(m.eds[e], os)) }
}

pub proof fn lemma_bcast(m: M, os: Seq<int>)
    requires inv_m(m), m.ct is Text,
    ensures inv_m(bcast(m, os)),
{
    let m2 = bcast(m, os);
    assert forall|e: nat| m2.eds.dom().contains(e) implies
        m2.ct is Text && inv(#[trigger] m2.eds[e]) && m2.eds[e].srv.cur == txt(m2) by {
        assert(m.eds.dom().contains(e));
        lemma_steps(m.eds[e], os);
    }
}

// A handler that makes the CRDT file binary or absent first drops every owner
// (`invalidate_editor_file`); a peer deleting an owned file is `bcast` of a delete-all instead.
pub open spec fn invalidate(m: M) -> M { M { ct: m.ct, eds: Map::empty() } }
pub open spec fn set_other(m: M) -> M { M { ct: Ct::Other, eds: m.eds } }
pub proof fn lemma_invalidate(m: M)
    requires inv_m(m), ensures inv_m(invalidate(m)),
{}
pub proof fn lemma_set_other(m: M)
    requires inv_m(m), m.eds.dom() =~= Set::<nat>::empty(), ensures inv_m(set_other(m)),
{}

// Close / failed send (`CloseEditorConnection`, `send_to_editor_client` error)
pub open spec fn close(m: M, e: nat) -> M { M { ct: m.ct, eds: m.eds.remove(e) } }
pub proof fn lemma_close(m: M, e: nat)
    requires inv_m(m), ensures inv_m(close(m, e)),
{
    let m2 = close(m, e);
    assert forall|f: nat| #[trigger] m2.eds.dom().contains(f) implies
        m2.ct is Text && inv(m2.eds[f]) && m2.eds[f].srv.cur == txt(m2) by {
        assert(f != e);
        assert(m.eds.dom().contains(f));
        assert(m2.eds[f] == m.eds[f]);
    }
}

// Open from editor `e` with buffer `content` (`OTServer::new(content)`), then the catch-up edit
// `od` the daemon sends when `content` differs from the CRDT (`process_component_message(Open)`),
// or a new CRDT file when there is no text there.
// ASSUMED (dissimilar::diff): `od` applied to `content` gives the CRDT text.
pub open spec fn open(m: M, e: nat, content: Seq<char>, od: int) -> M {
    match m.ct {
        Ct::Text(t) => M { ct: m.ct, eds: m.eds.insert(e,
            if content == t { init_w(content) } else { crdt_step(init_w(content), od) }) },
        Ct::Other => M { ct: Ct::Text(content), eds: m.eds.insert(e, init_w(content)) },
    }
}
pub open spec fn init_w(content: Seq<char>) -> W {
    W { srv: Srv { er: 0, dr: 0, q: Seq::empty(), lc: content, cur: content },
        ed: Ed { buf: content, rd: 0, re: 0 }, up: Seq::empty(), down: Seq::empty() }
}
pub proof fn lemma_open(m: M, e: nat, content: Seq<char>, od: int)
    requires inv_m(m), !m.eds.dom().contains(e),
        m.ct is Text ==> (content != txt(m) ==> ap(content, od) == txt(m)),
        // when the file is not text, nobody owns it (inv_m), nothing else to assume
    ensures inv_m(open(m, e, content, od)),
{
    lemma_init(content);
    let w0 = init_w(content);
    if m.ct is Text && content != txt(m) { lemma_crdt_step(w0, od); }
    let m2 = open(m, e, content, od);
    assert forall|f: nat| m2.eds.dom().contains(f) implies
        m2.ct is Text && inv(#[trigger] m2.eds[f]) && m2.eds[f].srv.cur == txt(m2) by {
        if f != e { assert(m.eds.dom().contains(f)); }
    }
}

// One editor's own moves (type, receive a daemon message).
pub open spec fn upd(m: M, e: nat, w: W) -> M { M { ct: m.ct, eds: m.eds.insert(e, w) } }
pub proof fn lemma_ed_local_m(m: M, e: nat, o: int)
    requires inv_m(m), m.eds.dom().contains(e), ensures inv_m(upd(m, e, ed_local(m.eds[e], o))),
{
    lemma_ed_local(m.eds[e], o);
    let m2 = upd(m, e, ed_local(m.eds[e], o));
    assert forall|f: nat| m2.eds.dom().contains(f) implies
        m2.ct is Text && inv(#[trigger] m2.eds[f]) && m2.eds[f].srv.cur == txt(m2) by {
        if f != e { assert(m.eds.dom().contains(f)); }
    }
}
pub proof fn lemma_ed_recv_m(m: M, e: nat)
    requires inv_m(m), m.eds.dom().contains(e), m.eds[e].down.len() > 0,
    ensures inv_m(upd(m, e, ed_recv(m.eds[e]))),
{
    lemma_ed_recv(m.eds[e]);
    let m2 = upd(m, e, ed_recv(m.eds[e]));
    assert forall|f: nat| m2.eds.dom().contains(f) implies
        m2.ct is Text && inv(#[trigger] m2.eds[f]) && m2.eds[f].srv.cur == txt(m2) by {
        if f != e { assert(m.eds.dom().contains(f)); }
    }
}

// The daemon handles editor `e`'s edit: its OT server transforms it (`apply_editor_operation`);
// the transformed op `o2` goes to the CRDT and is broadcast to every other owner
// (`process_component_message(Some(e), Edit)`).
pub open spec fn edit_out(w: W) -> int {
    let u = w.up[0];
    let k = (u.rev - confirmed(w.srv)) as int;
    tt(u.op, w.srv.q.subrange(k, w.srv.q.len() as int)).0
}
pub open spec fn from_editor(m: M, e: nat) -> M {
    let w = m.eds[e];
    let o2 = edit_out(w);
    M { ct: Ct::Text(ap(txt(m), o2)),
        eds: Map::new(m.eds.dom(),
            |f: nat| if f == e { srv_recv(w) } else { crdt_step(m.eds[f], o2) }) }
}
pub proof fn lemma_from_editor(m: M, e: nat)
    requires inv_m(m), m.eds.dom().contains(e), m.eds[e].up.len() > 0,
    ensures inv_m(from_editor(m, e)),
{
    let w = m.eds[e];
    lemma_srv_recv(w);
    let m2 = from_editor(m, e);
    let o2 = edit_out(w);
    assert(srv_recv(w).srv.cur == ap(w.srv.cur, o2));
    assert forall|f: nat| m2.eds.dom().contains(f) implies
        m2.ct is Text && inv(#[trigger] m2.eds[f]) && m2.eds[f].srv.cur == txt(m2) by {
        assert(m.eds.dom().contains(f));
        if f != e { lemma_crdt_step(m.eds[f], o2); }
    }
}

// ---------- results ----------
pub proof fn lemma_init_m(ct: Ct)
    ensures inv_m(M { ct, eds: Map::empty() }),
{}

// With nothing in flight to or from an owner, its buffer is the CRDT text.
pub proof fn theorem_quiescent_agreement_m(m: M, e: nat)
    requires inv_m(m), m.eds.dom().contains(e), m.eds[e].up.len() == 0, m.eds[e].down.len() == 0,
    ensures m.eds[e].ed.buf == txt(m),
{
    theorem_quiescent_agreement(m.eds[e]);
}

// Reopening a file on a connection whose earlier session has daemon messages in flight.
// The plugin protocol has no session id: a message is accepted iff its revision equals the
// editor's `revision.editor`. The old messages stay in `down`; the fresh session restarts at 0.
pub open spec fn reopen_no_barrier(w: W, content: Seq<char>) -> W {
    W { down: w.down, ..init_w(content) }
}
// With a barrier (the editor waits for the daemon's response to its close, so every earlier
// daemon message has been delivered; the daemon handled all earlier edits before the close),
// the reopened session is the initial one. This is the property the plugin must provide.
pub proof fn lemma_reopen_barrier(w: W, content: Seq<char>)
    requires inv(w),
    ensures inv(reopen_no_barrier(w, content)),
{
    lemma_init(content);
    assert(w.down =~= Seq::<Msg>::empty());
    assert(reopen_no_barrier(w, content) == init_w(content));
}

pub proof fn lemma_steps_one(w: W, o: int)
    ensures steps(w, seq![o]) == crdt_step(w, o),
{
    assert(seq![o].drop_first() =~= Seq::<int>::empty());
    assert(seq![o][0] == o);
    assert(steps(crdt_step(w, o), Seq::<int>::empty()) == crdt_step(w, o));
}

// A reachable concrete schedule (non-vacuity): editor opens, a peer's edit is broadcast, the
// editor receives it, types, the daemon transforms it and another editor sees it.
pub proof fn example_two_editors(a: Seq<char>, o1: int, o2: int)
    ensures true,
{
    let m0 = M { ct: Ct::Text(a), eds: Map::empty() };
    lemma_init_m(Ct::Text(a));
    let m1 = open(m0, 1, a, 0);
    lemma_open(m0, 1, a, 0);
    let m2 = open(m1, 2, a, 0);
    lemma_open(m1, 2, a, 0);
    assert(m2.eds.dom().contains(1) && m2.eds.dom().contains(2));
    let m3 = bcast(m2, seq![o1]);
    lemma_bcast(m2, seq![o1]);
    lemma_steps_one(m2.eds[1], o1);
    lemma_steps_one(m2.eds[2], o1);
    assert(m2.eds[1] == init_w(a) && m2.eds[2] == init_w(a));
    assert(m3.eds[1].down.len() == 1 && m3.eds[2].down.len() == 1);
    let m4 = upd(m3, 1, ed_local(m3.eds[1], o2));
    lemma_ed_local_m(m3, 1, o2);
    assert(m4.eds[1].up.len() == 1);
    let m5 = from_editor(m4, 1);
    lemma_from_editor(m4, 1);
    assert(m5.eds[2].down.len() == 2);
}

} // verus!
fn main() {}
