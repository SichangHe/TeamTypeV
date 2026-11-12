// Session freshness across close/reopen (authored by agents).
// The wire protocol has no session id. Plugins stay correct because the stream is FIFO:
// a session starts only at the answer to ITS open request (nvim: a per-open token; emacs: `teamtypev--session';
// VS Code: waits for `close'), and every daemon edit written before that answer is dropped.
// Model: editor->daemon FIFO `up`, daemon->editor FIFO `down`, epochs tagged by a GHOST id the plugin never sees.
// The daemon may FAIL an open (Git running, ignored file, not UTF-8: `Ans(e, false)`), and may forget a
// session while the editor keeps it (`invalidate_file`: `DaemonInvalidate`).
use vstd::prelude::*;
verus! {

pub enum Req { Open(nat), Close }
pub enum Msg { Ans(nat, bool), Edit(nat) }

pub struct S {
    pub up: Seq<Req>,
    pub down: Seq<Msg>,
    pub dcur: Option<nat>,       // daemon: epoch of the open session
    pub pending: Option<nat>,    // plugin: open sent, answer not seen
    pub live: Option<nat>,       // plugin: session started (the only thing the plugin knows is is_some())
    pub next: nat,
}

pub enum Act { EdOpen, EdClose, DaemonHandle, DaemonFailOpen, DaemonInvalidate, DaemonEdit, PluginHandle }

pub open spec fn is_ans(m: Msg, p: nat) -> bool { m is Ans && m->Ans_0 == p }

pub open spec fn wf(s: S) -> bool {
    (forall|i: int| #![trigger s.up[i]] 0 <= i < s.up.len() ==> (s.up[i] is Open ==> s.up[i]->Open_0 < s.next))
    && (forall|j: int| #![trigger s.down[j]] 0 <= j < s.down.len() ==> (s.down[j] is Ans ==> s.down[j]->Ans_0 < s.next))
    && (s.pending is Some ==> s.pending.unwrap() < s.next)
}

// the answer to the pending open sits at k; none before it; none after it, and after a successful answer only the session's edits
pub open spec fn answered(s: S, p: nat, k: int) -> bool {
    0 <= k < s.down.len() && s.down[k] is Ans && s.down[k]->Ans_0 == p
        && (forall|j: int| #![trigger s.down[j]] 0 <= j < k ==> !is_ans(s.down[j], p))
        && (forall|j: int| #![trigger s.down[j]] k < j < s.down.len() ==>
            !is_ans(s.down[j], p) && (s.down[k]->Ans_1 ==> s.down[j] == Msg::Edit(p)))
}
pub open spec fn no_ans(s: S, p: nat) -> bool {
    forall|j: int| #![trigger s.down[j]] 0 <= j < s.down.len() ==> !is_ans(s.down[j], p)
}
pub open spec fn only_edits(s: S, l: nat) -> bool {
    forall|j: int| #![trigger s.down[j]] 0 <= j < s.down.len() ==> s.down[j] == Msg::Edit(l)
}
pub open spec fn unique_open(s: S, p: nat) -> bool {
    forall|i: int| #![trigger s.up[i]] 0 <= i < s.up.len() - 1 ==> s.up[i] != Req::Open(p)
}

pub open spec fn phase_a(s: S) -> bool {
    s.pending is Some && s.live is None && s.up.len() > 0 && s.up.last() == Req::Open(s.pending.unwrap())
        && unique_open(s, s.pending.unwrap()) && no_ans(s, s.pending.unwrap())
}
pub open spec fn phase_b(s: S) -> bool {   // answered (successfully or not)
    s.pending is Some && s.live is None && s.up.len() == 0
        && (exists|k: int| answered(s, s.pending.unwrap(), k))
        // after a successful answer the daemon holds the session, or forgot it (invalidate_file)
        && (forall|k: int| #![trigger s.down[k]] answered(s, s.pending.unwrap(), k) && s.down[k]->Ans_1
                ==> (s.dcur == s.pending || s.dcur is None))
}
pub open spec fn phase_c(s: S) -> bool {
    s.pending is None && s.live is Some && s.up.len() == 0 && (s.dcur == s.live || s.dcur is None)
        && only_edits(s, s.live.unwrap())
}
pub open spec fn phase_d(s: S) -> bool { s.pending is None && s.live is None }

pub open spec fn inv(s: S) -> bool {
    wf(s) && (phase_a(s) || phase_b(s) || phase_c(s) || phase_d(s))
}

pub open spec fn step(s: S, a: Act, t: S, accepted_epoch: Option<nat>) -> bool {
    match a {
        Act::EdOpen => t == S { up: s.up.push(Req::Open(s.next)), pending: Some(s.next), live: None, next: s.next + 1, ..s }
                       && accepted_epoch is None,
        Act::EdClose => t == S { up: s.up.push(Req::Close), pending: None, live: None, ..s } && accepted_epoch is None,
        Act::DaemonHandle => s.up.len() > 0 && accepted_epoch is None && match s.up[0] {
            Req::Open(e) => t == S { up: s.up.drop_first(), dcur: Some(e), down: s.down.push(Msg::Ans(e, true)), ..s },
            Req::Close => t == S { up: s.up.drop_first(), dcur: None, ..s },
        },
        // a failed open (Git running, ignored, not UTF-8): an error answer, no session
        Act::DaemonFailOpen => s.up.len() > 0 && accepted_epoch is None && s.up[0] is Open
            && t == S { up: s.up.drop_first(), down: s.down.push(Msg::Ans(s.up[0]->Open_0, false)), ..s },
        // `invalidate_file`: the daemon forgets the session while the editor keeps the file open
        Act::DaemonInvalidate => t == S { dcur: None, ..s } && accepted_epoch is None,
        Act::DaemonEdit => s.dcur is Some && accepted_epoch is None
            && t == S { down: s.down.push(Msg::Edit(s.dcur.unwrap())), ..s },
        Act::PluginHandle => s.down.len() > 0 && match s.down[0] {
            Msg::Ans(e, ok) => accepted_epoch is None && (
                if s.pending == Some(e) {
                    t == S { down: s.down.drop_first(), pending: None, live: if ok { Some(e) } else { None }, ..s }
                } else { t == S { down: s.down.drop_first(), ..s } }),
            // the plugin applies an edit iff it has a live session; it never sees the epoch
            Msg::Edit(x) => t == S { down: s.down.drop_first(), ..s }
                            && (if s.live is Some { accepted_epoch == Some(x) } else { accepted_epoch is None }),
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_edopen(s: S, t: S)
    requires inv(s), step(s, Act::EdOpen, t, None),
    ensures inv(t)
{
    let p = s.next;
    assert(wf(t)) by {
        assert forall|i: int| 0 <= i < t.up.len() implies (t.up[i] is Open ==> t.up[i]->Open_0 < t.next) by {
            if i < s.up.len() { assert(t.up[i] == s.up[i]); }
        }
        assert forall|j: int| 0 <= j < t.down.len() implies (t.down[j] is Ans ==> t.down[j]->Ans_0 < t.next) by {
            assert(t.down[j] == s.down[j]);
        }
    }
    assert(unique_open(t, p)) by {
        assert forall|i: int| 0 <= i < t.up.len() - 1 implies t.up[i] != Req::Open(p) by {
            assert(t.up[i] == s.up[i]);
        }
    }
    assert(no_ans(t, p)) by {
        assert forall|j: int| 0 <= j < t.down.len() implies !is_ans(t.down[j], p) by {
            assert(t.down[j] == s.down[j]);
        }
    }
    assert(t.up.last() == Req::Open(p));
    assert(phase_a(t));
}

proof fn lemma_edclose(s: S, t: S)
    requires inv(s), step(s, Act::EdClose, t, None),
    ensures inv(t)
{
    assert(wf(t)) by {
        assert forall|i: int| 0 <= i < t.up.len() implies (t.up[i] is Open ==> t.up[i]->Open_0 < t.next) by {
            if i < s.up.len() { assert(t.up[i] == s.up[i]); }
        }
    }
    assert(phase_d(t));
}

#[verifier::spinoff_prover]
proof fn lemma_daemon_handle(s: S, t: S)
    requires inv(s), step(s, Act::DaemonHandle, t, None),
    ensures inv(t)
{
    assert(wf(t)) by {
        assert forall|i: int| 0 <= i < t.up.len() implies (t.up[i] is Open ==> t.up[i]->Open_0 < t.next) by {
            assert(t.up[i] == s.up[i + 1]);
        }
        assert forall|j: int| 0 <= j < t.down.len() implies (t.down[j] is Ans ==> t.down[j]->Ans_0 < t.next) by {
            if j < s.down.len() { assert(t.down[j] == s.down[j]); }
            else if let Req::Open(e) = s.up[0] { assert(e < s.next) by { assert(s.up[0] is Open); } }
        }
    }
    if phase_a(s) {
        let p = s.pending.unwrap();
        if s.up.len() == 1 {
            let k = s.down.len() as int;
            assert(s.up[0] == Req::Open(p));
            assert(answered(t, p, k)) by {
                assert forall|j: int| 0 <= j < k implies !is_ans(t.down[j], p) by { assert(t.down[j] == s.down[j]); }
            }
            assert(t.dcur == Some(p));
            assert(phase_b(t)) by {
                assert forall|k2: int| answered(t, p, k2) && t.down[k2]->Ans_1 implies (t.dcur == t.pending || t.dcur is None) by {}
            }
        } else {
            assert(t.up.last() == s.up.last());
            assert(unique_open(t, p)) by {
                assert forall|i: int| 0 <= i < t.up.len() - 1 implies t.up[i] != Req::Open(p) by { assert(t.up[i] == s.up[i + 1]); }
            }
            assert(no_ans(t, p)) by {
                assert forall|j: int| 0 <= j < t.down.len() implies !is_ans(t.down[j], p) by {
                    if j < s.down.len() { assert(t.down[j] == s.down[j]); }
                    else { assert(s.up[0] is Open); assert(s.up[0]->Open_0 != p) by { assert(s.up[0] != Req::Open(p)); } }
                }
            }
            assert(phase_a(t));
        }
    }
    // phases B and C have no pending requests (up empty), so there is nothing to handle; D is unconstrained
    if phase_d(s) { assert(phase_d(t)); }
}

#[verifier::spinoff_prover]
proof fn lemma_daemon_failopen(s: S, t: S)
    requires inv(s), step(s, Act::DaemonFailOpen, t, None),
    ensures inv(t)
{
    assert(wf(t)) by {
        assert forall|i: int| 0 <= i < t.up.len() implies (t.up[i] is Open ==> t.up[i]->Open_0 < t.next) by {
            assert(t.up[i] == s.up[i + 1]);
        }
        assert forall|j: int| 0 <= j < t.down.len() implies (t.down[j] is Ans ==> t.down[j]->Ans_0 < t.next) by {
            if j < s.down.len() { assert(t.down[j] == s.down[j]); }
        }
    }
    if phase_a(s) {
        let p = s.pending.unwrap();
        if s.up.len() == 1 {
            let k = s.down.len() as int;
            assert(s.up[0] == Req::Open(p));
            assert(answered(t, p, k)) by {
                assert forall|j: int| 0 <= j < k implies !is_ans(t.down[j], p) by { assert(t.down[j] == s.down[j]); }
            }
            assert(t.down[k] == Msg::Ans(p, false));
            assert(phase_b(t)) by {
                assert forall|k2: int| answered(t, p, k2) && t.down[k2]->Ans_1 implies (t.dcur == t.pending || t.dcur is None) by {
                    // only one answer to p exists, and it is the failure
                    assert(is_ans(t.down[k2], p));
                    if k2 < k { assert(false); }
                    if k2 > k { assert(false); }
                }
            }
        } else {
            assert(t.up.last() == s.up.last());
            assert(unique_open(t, p)) by {
                assert forall|i: int| 0 <= i < t.up.len() - 1 implies t.up[i] != Req::Open(p) by { assert(t.up[i] == s.up[i + 1]); }
            }
            assert(no_ans(t, p)) by {
                assert forall|j: int| 0 <= j < t.down.len() implies !is_ans(t.down[j], p) by {
                    if j < s.down.len() { assert(t.down[j] == s.down[j]); }
                    else { assert(s.up[0]->Open_0 != p) by { assert(s.up[0] != Req::Open(p)); } }
                }
            }
            assert(phase_a(t));
        }
    }
    if phase_d(s) { assert(phase_d(t)); }
}

proof fn lemma_invalidate(s: S, t: S)
    requires inv(s), step(s, Act::DaemonInvalidate, t, None),
    ensures inv(t)
{
    if phase_a(s) { assert(phase_a(t)); }
    if phase_c(s) { assert(phase_c(t)); }
    if phase_d(s) { assert(phase_d(t)); }
    if phase_b(s) {
        let p = s.pending.unwrap();
        let k0 = choose|k: int| answered(s, p, k);
        assert(answered(t, p, k0));
        assert(phase_b(t)) by {
            assert forall|k: int| answered(t, p, k) && t.down[k]->Ans_1 implies (t.dcur == t.pending || t.dcur is None) by {}
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_daemon_edit(s: S, t: S)
    requires inv(s), step(s, Act::DaemonEdit, t, None),
    ensures inv(t)
{
    let x = s.dcur.unwrap();
    assert(wf(t)) by {
        assert forall|j: int| 0 <= j < t.down.len() implies (t.down[j] is Ans ==> t.down[j]->Ans_0 < t.next) by {
            if j < s.down.len() { assert(t.down[j] == s.down[j]); }
        }
    }
    if phase_a(s) {
        let p = s.pending.unwrap();
        assert(no_ans(t, p)) by {
            assert forall|j: int| 0 <= j < t.down.len() implies !is_ans(t.down[j], p) by {
                if j < s.down.len() { assert(t.down[j] == s.down[j]); }
            }
        }
        assert(unique_open(t, p));
        assert(phase_a(t));
    }
    if phase_b(s) {
        let p = s.pending.unwrap();
        let k = choose|k: int| answered(s, p, k);
        assert(answered(t, p, k)) by {
            assert forall|j: int| 0 <= j < k implies !is_ans(t.down[j], p) by { assert(t.down[j] == s.down[j]); }
            assert forall|j: int| k < j < t.down.len() implies !is_ans(t.down[j], p) && (t.down[k]->Ans_1 ==> t.down[j] == Msg::Edit(p)) by {
                if j < s.down.len() { assert(t.down[j] == s.down[j]); }
                else { assert(t.down[j] == Msg::Edit(x)); if t.down[k]->Ans_1 { assert(s.dcur == s.pending); } }
            }
        }
        assert(phase_b(t)) by {
            assert forall|k2: int| answered(t, p, k2) && t.down[k2]->Ans_1 implies (t.dcur == t.pending || t.dcur is None) by {
                assert(t.down[k2] == s.down[k2] || k2 >= s.down.len());
                if k2 < s.down.len() { assert(answered(s, p, k2)) by {
                    assert forall|j: int| k2 < j < s.down.len() implies !is_ans(s.down[j], p) && (s.down[k2]->Ans_1 ==> s.down[j] == Msg::Edit(p)) by {
                        assert(t.down[j] == s.down[j]); } } }
            }
        }
    }
    if phase_c(s) {
        assert(only_edits(t, s.live.unwrap())) by {
            assert forall|j: int| 0 <= j < t.down.len() implies t.down[j] == Msg::Edit(s.live.unwrap()) by {
                if j < s.down.len() { assert(t.down[j] == s.down[j]); }
            }
        }
        assert(phase_c(t));
    }
    if phase_d(s) { assert(phase_d(t)); }
}

#[verifier::spinoff_prover]
proof fn lemma_plugin_handle(s: S, t: S, ae: Option<nat>)
    requires inv(s), step(s, Act::PluginHandle, t, ae),
    ensures inv(t)
{
    assert(wf(t)) by {
        assert forall|j: int| 0 <= j < t.down.len() implies (t.down[j] is Ans ==> t.down[j]->Ans_0 < t.next) by { assert(t.down[j] == s.down[j + 1]); }
    }
    if phase_a(s) {
        let p = s.pending.unwrap();
        assert(no_ans(t, p)) by {
            assert forall|j: int| 0 <= j < t.down.len() implies !is_ans(t.down[j], p) by { assert(t.down[j] == s.down[j + 1]); }
        }
        assert(phase_a(t));
    }
    if phase_b(s) {
        let p = s.pending.unwrap();
        let k = choose|k: int| answered(s, p, k);
        if k == 0 {
            let ok = s.down[0]->Ans_1;
            if ok {
                assert(only_edits(t, p)) by {
                    assert forall|j: int| 0 <= j < t.down.len() implies t.down[j] == Msg::Edit(p) by { assert(t.down[j] == s.down[j + 1]); }
                }
                assert(s.dcur == s.pending || s.dcur is None);
                assert(phase_c(t));
            } else {
                assert(phase_d(t));
            }
        } else {
            assert(answered(t, p, k - 1)) by {
                assert(t.down[k - 1] == s.down[k]);
                assert forall|j: int| 0 <= j < k - 1 implies !is_ans(t.down[j], p) by { assert(t.down[j] == s.down[j + 1]); }
                assert forall|j: int| k - 1 < j < t.down.len() implies !is_ans(t.down[j], p) && (t.down[k - 1]->Ans_1 ==> t.down[j] == Msg::Edit(p)) by { assert(t.down[j] == s.down[j + 1]); }
            }
            assert(phase_b(t)) by {
                assert forall|k2: int| answered(t, p, k2) && t.down[k2]->Ans_1 implies (t.dcur == t.pending || t.dcur is None) by {
                    assert(answered(s, p, k2 + 1)) by {
                        assert(t.down[k2] == s.down[k2 + 1]);
                        assert forall|j: int| 0 <= j < k2 + 1 implies !is_ans(s.down[j], p) by {
                            if j > 0 { assert(t.down[j - 1] == s.down[j]); }
                            else { assert(!is_ans(s.down[0], p)) by { assert(k > 0); } }
                        }
                        assert forall|j: int| k2 + 1 < j < s.down.len() implies !is_ans(s.down[j], p) && (s.down[k2 + 1]->Ans_1 ==> s.down[j] == Msg::Edit(p)) by {
                            assert(t.down[j - 1] == s.down[j]); }
                    }
                }
            }
        }
    }
    if phase_c(s) { assert(phase_c(t)) by { assert forall|j: int| 0 <= j < t.down.len() implies t.down[j] == Msg::Edit(s.live.unwrap()) by { assert(t.down[j] == s.down[j + 1]); } } }
    if phase_d(s) { assert(phase_d(t)); }
}

// every step preserves the invariant
proof fn lemma_inv_step(s: S, a: Act, t: S, ae: Option<nat>)
    requires inv(s), step(s, a, t, ae),
    ensures inv(t)
{
    match a {
        Act::EdOpen => lemma_edopen(s, t),
        Act::EdClose => lemma_edclose(s, t),
        Act::DaemonHandle => lemma_daemon_handle(s, t),
        Act::DaemonFailOpen => lemma_daemon_failopen(s, t),
        Act::DaemonInvalidate => lemma_invalidate(s, t),
        Act::DaemonEdit => lemma_daemon_edit(s, t),
        Act::PluginHandle => lemma_plugin_handle(s, t, ae),
    }
}

// Freshness: any edit the plugin applies belongs to the session of the latest open it started.
proof fn lemma_fresh(s: S, a: Act, t: S, x: nat)
    requires inv(s), step(s, a, t, Some(x)),
    ensures s.live == Some(x), s.pending is None
{
    assert(a is PluginHandle);
    assert(s.live is Some);
    assert(phase_c(s));
    assert(s.down[0] == Msg::Edit(s.live.unwrap()));
}

// A stale answer (not for the pending open) never starts a session; this is the rule the plugins'
// per-open token / session object implements.
proof fn lemma_stale_answer_ignored(s: S, t: S, e: nat, ok: bool)
    requires s.down.len() > 0, s.down[0] == Msg::Ans(e, ok), s.pending != Some(e), step(s, Act::PluginHandle, t, None),
    ensures t.live == s.live, t.pending == s.pending
{}

// A failed answer never starts a session.
proof fn lemma_failed_answer_no_session(s: S, t: S, e: nat)
    requires s.down.len() > 0, s.down[0] == Msg::Ans(e, false), s.live is None, step(s, Act::PluginHandle, t, None),
    ensures t.live is None
{}

// Non-vacuity of `lemma_fresh`: a state satisfying `inv` where the plugin applies an edit.
proof fn lemma_fresh_nonvacuous()
    ensures exists|s: S, t: S| inv(s) && #[trigger] step(s, Act::PluginHandle, t, Some(0nat))
{
    let s = S { up: seq![], down: seq![Msg::Edit(0)], dcur: Some(0), pending: None, live: Some(0), next: 1 };
    let t = S { down: s.down.drop_first(), ..s };
    assert(only_edits(s, 0));
    assert(phase_c(s));
    assert(step(s, Act::PluginHandle, t, Some(0nat)));
}

// The invariant holds initially (no session), so every reachable state satisfies it.
proof fn lemma_init(s: S)
    requires s.up.len() == 0, s.down.len() == 0, s.dcur is None, s.pending is None, s.live is None,
    ensures inv(s)
{
    assert(wf(s));
    assert(phase_d(s));
}

// ---------------------------------------------------------------------------------------------
// VS Code variant (vscode-plugin/src/extension.ts, `startSharedSession`, `processUserClose`,
// `waitForClosedSession`). The session is live at the open SEND (`ot_states[uri]` is created before
// `open` is sent, and the handoff edit rides at revision 0). Safety comes instead from `close` being a
// REQUEST: a reopen waits until the daemon answered the previous `close` (and the queued handlers ran);
// the daemon writes that answer after every edit of the closed session and sends none after it.
// A failed open deletes the session (`if (client.ot_states[uri] === state) delete ...`).
pub mod vscode {
use vstd::prelude::*;

pub enum VReq { Open(nat), Close }
pub enum VMsg { Ans(nat, bool), CloseAns, Edit(nat) }

pub struct V {
    pub up: Seq<VReq>,
    pub down: Seq<VMsg>,
    pub dcur: Option<nat>,
    pub live: Option<nat>,   // plugin: `ot_states[uri]` exists (ghost epoch)
    pub closing: bool,       // plugin: a `close` request is unanswered (`closingDocuments`)
    pub next: nat,
}

pub enum VAct { EdOpen, EdClose, DaemonHandle, DaemonFailOpen, DaemonInvalidate, DaemonEdit, PluginHandle }

pub open spec fn all_edits(d: Seq<VMsg>, l: nat) -> bool {
    forall|j: int| #![trigger d[j]] 0 <= j < d.len() ==> d[j] == VMsg::Edit(l)
}
pub open spec fn no_close_ans(d: Seq<VMsg>) -> bool {
    forall|j: int| #![trigger d[j]] 0 <= j < d.len() ==> !(d[j] is CloseAns)
}
pub open spec fn dcur_ok(v: V, l: nat) -> bool { v.dcur == Some(l) || v.dcur is None }

pub open spec fn idle(v: V) -> bool {
    v.live is None && !v.closing && v.up.len() == 0 && v.down.len() == 0 && v.dcur is None
}
pub open spec fn live_phase(v: V) -> bool {
    v.live is Some && !v.closing && {
        let l = v.live.unwrap();
        // open sent, not handled
        (v.up =~= seq![VReq::Open(l)] && v.down.len() == 0 && v.dcur is None)
        // success answer pending, then the session's edits
        || (v.up.len() == 0 && v.down.len() > 0 && v.down[0] == VMsg::Ans(l, true)
            && all_edits(v.down.drop_first(), l) && dcur_ok(v, l))
        // failure answer pending
        || (v.up.len() == 0 && v.down =~= seq![VMsg::Ans(l, false)] && v.dcur is None)
        // answered
        || (v.up.len() == 0 && all_edits(v.down, l) && dcur_ok(v, l))
    }
}
pub open spec fn closing_phase(v: V) -> bool {
    v.live is None && v.closing && (
        (exists|l: nat| v.up =~= seq![VReq::Open(l), VReq::Close]) && v.down.len() == 0 && v.dcur is None
        || (v.up =~= seq![VReq::Close] && no_close_ans(v.down))
        || (v.up.len() == 0 && v.down.len() > 0 && v.down.last() is CloseAns
            && no_close_ans(v.down.drop_last()) && v.dcur is None)
    )
}
pub open spec fn vinv(v: V) -> bool { idle(v) || live_phase(v) || closing_phase(v) }

pub open spec fn vstep(v: V, a: VAct, t: V, accepted: Option<nat>) -> bool {
    match a {
        // `waitForClosedSession`: no open while a close is unanswered; one session per uri
        VAct::EdOpen => v.live is None && !v.closing && accepted is None
            && t == V { up: v.up.push(VReq::Open(v.next)), live: Some(v.next), next: v.next + 1, ..v },
        // `processUserClose` only for tracked documents
        VAct::EdClose => v.live is Some && accepted is None
            && t == V { up: v.up.push(VReq::Close), live: None, closing: true, ..v },
        VAct::DaemonHandle => v.up.len() > 0 && accepted is None && match v.up[0] {
            VReq::Open(e) => t == V { up: v.up.drop_first(), dcur: Some(e), down: v.down.push(VMsg::Ans(e, true)), ..v },
            VReq::Close => t == V { up: v.up.drop_first(), dcur: None, down: v.down.push(VMsg::CloseAns), ..v },
        },
        VAct::DaemonFailOpen => v.up.len() > 0 && accepted is None && v.up[0] is Open
            && t == V { up: v.up.drop_first(), down: v.down.push(VMsg::Ans(v.up[0]->Open_0, false)), ..v },
        VAct::DaemonInvalidate => t == V { dcur: None, ..v } && accepted is None,
        VAct::DaemonEdit => v.dcur is Some && accepted is None
            && t == V { down: v.down.push(VMsg::Edit(v.dcur.unwrap())), ..v },
        VAct::PluginHandle => v.down.len() > 0 && match v.down[0] {
            VMsg::Ans(e, ok) => accepted is None && t == V { down: v.down.drop_first(),
                live: if !ok && v.live == Some(e) { None } else { v.live }, ..v },
            VMsg::CloseAns => accepted is None && t == V { down: v.down.drop_first(), closing: false, ..v },
            // applied iff `ot_states[uri]` exists; the plugin never sees the epoch
            VMsg::Edit(x) => t == V { down: v.down.drop_first(), ..v }
                && (if v.live is Some { accepted == Some(x) } else { accepted is None }),
        },
    }
}

proof fn lemma_v_init(v: V)
    requires v.up.len() == 0, v.down.len() == 0, v.dcur is None, v.live is None, !v.closing,
    ensures vinv(v)
{}

#[verifier::spinoff_prover]
proof fn lemma_v_step(v: V, a: VAct, t: V, ae: Option<nat>)
    requires vinv(v), vstep(v, a, t, ae),
    ensures vinv(t)
{
    match a {
        VAct::EdOpen => {
            assert(t.up =~= seq![VReq::Open(v.next)]);
            assert(live_phase(t));
        }
        VAct::EdClose => {
            let l = v.live.unwrap();
            if v.up.len() == 1 {
                assert(t.up =~= seq![VReq::Open(l), VReq::Close]);
                assert(closing_phase(t));
            } else {
                assert(t.up =~= seq![VReq::Close]);
                assert(no_close_ans(t.down)) by {
                    assert forall|j: int| 0 <= j < t.down.len() implies !(t.down[j] is CloseAns) by {
                        if v.down.len() > 0 && v.down[0] is Ans {
                            if j > 0 { assert(t.down[j] == v.down.drop_first()[j - 1]); }
                        } else if v.down =~= seq![VMsg::Ans(l, false)] {
                        } else { assert(all_edits(v.down, l)); }
                    }
                }
                assert(closing_phase(t));
            }
        }
        VAct::DaemonHandle => {
            if live_phase(v) {
                let l = v.live.unwrap();
                assert(v.up[0] == VReq::Open(l));
                assert(t.down =~= seq![VMsg::Ans(l, true)]);
                assert(all_edits(t.down.drop_first(), l));
                assert(live_phase(t));
            } else {
                assert(closing_phase(v));
                if v.up.len() == 2 {
                    let l = choose|l: nat| v.up =~= seq![VReq::Open(l), VReq::Close];
                    assert(v.up[0] == VReq::Open(l));
                    assert(t.up =~= seq![VReq::Close]);
                    assert(no_close_ans(t.down)) by {
                        assert forall|j: int| 0 <= j < t.down.len() implies !(t.down[j] is CloseAns) by {}
                    }
                    assert(closing_phase(t));
                } else {
                    assert(v.up[0] == VReq::Close);
                    assert(t.down.drop_last() =~= v.down);
                    assert(closing_phase(t));
                }
            }
        }
        VAct::DaemonFailOpen => {
            if live_phase(v) {
                let l = v.live.unwrap();
                assert(t.down =~= seq![VMsg::Ans(l, false)]);
                assert(live_phase(t));
            } else {
                let l = choose|l: nat| v.up =~= seq![VReq::Open(l), VReq::Close];
                assert(t.up =~= seq![VReq::Close]);
                assert(no_close_ans(t.down)) by {
                    assert forall|j: int| 0 <= j < t.down.len() implies !(t.down[j] is CloseAns) by {}
                }
                assert(closing_phase(t));
            }
        }
        VAct::DaemonInvalidate => {
            if closing_phase(v) && v.up.len() == 2 {
                let l = choose|l: nat| v.up =~= seq![VReq::Open(l), VReq::Close];
                assert(t.up =~= seq![VReq::Open(l), VReq::Close]);
            }
            assert(vinv(t));
        }
        VAct::DaemonEdit => {
            let x = v.dcur.unwrap();
            if live_phase(v) {
                let l = v.live.unwrap();
                assert(x == l);
                if v.down.len() > 0 && v.down[0] == VMsg::Ans(l, true) {
                    assert(t.down.drop_first() =~= v.down.drop_first().push(VMsg::Edit(l)));
                    assert(all_edits(t.down.drop_first(), l)) by {
                        assert forall|j: int| 0 <= j < t.down.drop_first().len() implies t.down.drop_first()[j] == VMsg::Edit(l) by {
                            if j < v.down.drop_first().len() { assert(t.down.drop_first()[j] == v.down.drop_first()[j]); }
                        }
                    }
                } else {
                    assert(all_edits(v.down, l));
                    assert(all_edits(t.down, l)) by {
                        assert forall|j: int| 0 <= j < t.down.len() implies t.down[j] == VMsg::Edit(l) by {
                            if j < v.down.len() { assert(t.down[j] == v.down[j]); }
                        }
                    }
                }
                assert(live_phase(t));
            } else {
                assert(closing_phase(v));
                assert(v.up =~= seq![VReq::Close]);
                assert(no_close_ans(t.down)) by {
                    assert forall|j: int| 0 <= j < t.down.len() implies !(t.down[j] is CloseAns) by {
                        if j < v.down.len() { assert(t.down[j] == v.down[j]); }
                    }
                }
                assert(closing_phase(t));
            }
        }
        VAct::PluginHandle => {
            if live_phase(v) {
                let l = v.live.unwrap();
                if v.down[0] == VMsg::Ans(l, true) {
                    assert(t.down =~= v.down.drop_first());
                    assert(live_phase(t));
                } else if v.down =~= seq![VMsg::Ans(l, false)] {
                    assert(idle(t));
                } else {
                    assert(all_edits(v.down, l));
                    assert(v.down[0] == VMsg::Edit(l));
                    assert(all_edits(t.down, l)) by {
                        assert forall|j: int| 0 <= j < t.down.len() implies t.down[j] == VMsg::Edit(l) by {
                            assert(t.down[j] == v.down[j + 1]);
                        }
                    }
                    assert(live_phase(t));
                }
            } else {
                assert(closing_phase(v));
                if v.up.len() == 0 {
                    if v.down.len() == 1 {
                        assert(v.down[0] == v.down.last());
                        assert(idle(t));
                    } else {
                        assert(!(v.down[0] is CloseAns)) by { assert(v.down[0] == v.down.drop_last()[0]); }
                        assert(t.down.last() == v.down.last());
                        assert(no_close_ans(t.down.drop_last())) by {
                            assert forall|j: int| 0 <= j < t.down.drop_last().len() implies !(t.down.drop_last()[j] is CloseAns) by {
                                assert(t.down.drop_last()[j] == v.down.drop_last()[j + 1]);
                            }
                        }
                        assert(closing_phase(t));
                    }
                } else {
                    assert(v.up =~= seq![VReq::Close]);
                    assert(!(v.down[0] is CloseAns));
                    assert(no_close_ans(t.down)) by {
                        assert forall|j: int| 0 <= j < t.down.len() implies !(t.down[j] is CloseAns) by {
                            assert(t.down[j] == v.down[j + 1]);
                        }
                    }
                    assert(closing_phase(t));
                }
            }
        }
    }
}

// Freshness (VS Code): an applied daemon edit belongs to the live session.
proof fn lemma_v_fresh(v: V, a: VAct, t: V, x: nat)
    requires vinv(v), vstep(v, a, t, Some(x)),
    ensures v.live == Some(x)
{
    assert(a is PluginHandle);
    let l = v.live.unwrap();
    assert(live_phase(v));
    if v.down.len() > 0 && v.down[0] is Ans {
    } else if v.down =~= seq![VMsg::Ans(l, false)] {
    } else { assert(all_edits(v.down, l)); assert(v.down[0] == VMsg::Edit(l)); }
}

// Non-vacuity: the invariant admits a state where an edit is actually applied.
proof fn lemma_v_nonvacuous()
    ensures exists|v: V, t: V| vinv(v) && #[trigger] vstep(v, VAct::PluginHandle, t, Some(0nat))
{
    let v = V { up: seq![], down: seq![VMsg::Edit(0)], dcur: Some(0), live: Some(0), closing: false, next: 1 };
    let t = V { down: v.down.drop_first(), ..v };
    assert(all_edits(v.down, 0));
    assert(live_phase(v));
    assert(vstep(v, VAct::PluginHandle, t, Some(0nat)));
}

} // mod vscode

} // verus!
fn main() {}
