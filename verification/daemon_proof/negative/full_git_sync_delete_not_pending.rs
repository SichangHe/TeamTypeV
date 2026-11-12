// (authored by agents) Verus model of one shared file's disk coherence in daemon.rs with outside
// writes, file creation/removal, editor ownership, failed writes and Git deferral. Extends
// disk_proof.rs (see DESIGN.md). Texts are opaque ints; `None` = no file.
use vstd::prelude::*;

verus! {

pub uninterp spec fn merge(base: int, cur: int, outside: int) -> int;
pub uninterp spec fn empty_t() -> int; // the empty text, what `merge_disk_content(path, vec![])` merges in

// ASSUMED, tested by `merging_an_outside_change_into_unchanged_shared_text_gives_the_outside_text`
// (daemon_race_tests.rs, 3000 random cases): merging into an unchanged shared text yields the outside text.
#[verifier::external_body]
pub proof fn axiom_merge_clean(b: int, o: int)
    ensures merge(b, b, o) == o,
{}

pub enum Pc { Idle, W0, W1, W2, W3, W4 }

pub struct Fl {
    pub pc: Pc,
    pub c: Option<int>,  // CRDT text (None: not in the CRDT)
    pub dc: Option<int>, // disk_content entry
    pub d: Option<int>,  // real file
    pub n: nat,          // queued watcher events
    pub lc: int,         // `content` snapshot of the write loop
    pub wat: bool,       // run started by a watcher event
    pub wr: bool,        // after the read/merge step, continue with the write (false for Removed events, rescans)
    pub pend: bool,      // a write or removal is deferred (Git) or failed; rescan/finish retries
    pub own: bool,       // some editor has the file open (`!DocumentActor::owns`)
    pub git: bool,       // git_running
    pub lost: bool,      // ghost: a write displaced outside bytes (differing from the record, not the
                         // empty file without a record) without merging them into the shared text
}

pub enum Act {
    Outside(Option<int>), // another process (or Git) creates, writes or removes the file; event queued
    CrdtChange(int),      // sync message or editor edit changes the text; handler writes (or defers during Git)
    SyncDelete,           // a peer deleted the file, daemon-owned (an owned file is recreated empty: CrdtChange)
    Watch,                // actor takes a watcher event
    MergeOnly,            // RescanFiles / GitHeads / Open-Edit pre-check: read + merge, no write
    Step,                 // next step of the running handler
    Fail,                 // the write at W3 fails
    FailRemove,           // the unlink of a peer-deleted file fails (remove_disk_file keeps the last-seen record and defers)
    FailSave,             // `persist` fails right after W3 displaced bytes (ensure_file_has_bytes returns Err)
    Retry,                // rescan retries a pending write
    Own(bool),            // an editor opens (true) or closes (false: release_files writes the file)
    GitStart,
    GitFinish,
}

// the read/merge step: `file_created_or_changed` + `remove_file` + `merge_disk_content`
pub open spec fn read_merge(s: Fl) -> Fl {
    match s.d {
        Some(t) => if s.dc == Some(t) { s } else {
            match (s.c, s.dc) {
                (Some(cur), Some(b)) => Fl { c: Some(merge(b, cur, t)), dc: Some(t), ..s },
                _ => Fl { c: Some(t), dc: Some(t), ..s },
            }
        },
        None => if s.own {
            match (s.c, s.dc) {
                (Some(cur), Some(b)) => Fl { c: Some(merge(b, cur, empty_t())), dc: Some(empty_t()), ..s },
                _ => Fl { c: Some(empty_t()), dc: Some(empty_t()), ..s },
            }
        } else if s.pend && s.dc is None { s } // rescan keeps a file whose write is deferred
        else { Fl { c: None, dc: None, ..s } },
    }
}

// the bytes replaced at W3 were an outside write that carried content
pub open spec fn displaced_unmerged(s: Fl) -> bool {
    s.d is Some && s.d != s.dc && !(s.dc is None && s.d == Some(empty_t()))
}

// a deferred or immediate removal of a daemon-owned file deleted by a peer (c is None)
pub open spec fn remove_or_merge(s: Fl) -> Fl {
    match s.d {
        Some(x) => if s.dc != Some(x) { Fl { c: Some(x), dc: Some(x), ..s } }
            else { Fl { c: None, d: None, dc: None, lost: s.lost || displaced_unmerged(s), ..s } },
        None => Fl { c: None, d: None, dc: None, ..s },
    }
}

pub open spec fn enabled(s: Fl, a: Act) -> bool {
    match a {
        Act::Outside(_) => true,
        Act::CrdtChange(_) => s.pc is Idle,
        Act::SyncDelete => s.pc is Idle && s.c is Some && !s.own,
        Act::Watch => s.pc is Idle && s.n > 0,
        Act::MergeOnly => s.pc is Idle && !s.git,
        Act::Step => !(s.pc is Idle),
        Act::Fail => s.pc is W3,
        Act::FailSave => s.pc is W3,
        Act::FailRemove => s.pc is Idle && s.c is Some && !s.own && !s.git,
        Act::Retry => s.pc is Idle && s.pend && !s.git,
        Act::Own(b) => s.pc is Idle && (b ==> s.c is Some),
        Act::GitStart => s.pc is Idle && !s.git,
        Act::GitFinish => s.pc is Idle && s.git,
    }
}

// `replace_file_keeping` + merge of the displaced bytes (`ensure_file_has_bytes`)
pub open spec fn w3(s: Fl) -> Fl {
    match (s.d, s.dc) {
            (Some(x), Some(b)) if x != b =>
                Fl { pc: Pc::W4, c: Some(merge(b, s.lc, x)), d: Some(s.lc), dc: Some(s.lc), ..s },
            // no record (file created outside, its event not yet handled): `merge_disk_content`
            // without a base keeps the outside bytes (fix on branch tvd-daemon-proof)
            (Some(x), None) if x != empty_t() =>
                Fl { pc: Pc::W4, c: if s.c == Some(x) { s.c } else { Some(x) }, d: Some(s.lc), dc: Some(s.lc), ..s },
            _ => Fl { pc: Pc::W4, d: Some(s.lc), dc: Some(s.lc), lost: s.lost || displaced_unmerged(s), ..s },
        }
}

pub open spec fn step(s: Fl, a: Act) -> Fl {
    match a {
        Act::Outside(t) => Fl { d: t, n: s.n + 1, ..s },
        Act::CrdtChange(c2) => if s.git { Fl { c: Some(c2), pend: true, ..s } }
            else { Fl { pc: Pc::W0, c: Some(c2), wat: false, wr: true, ..s } },
        // FileRemoval: delete only when the disk equals the record, else merge the outside bytes
        // back (fix 3577382, `unhandled_outside_write`); `lost` checks the delete
        Act::SyncDelete => if s.git { Fl { c: None, pend: false, ..s } }
            else { remove_or_merge(s) },
        Act::Watch => if s.git { Fl { n: (s.n - 1) as nat, ..s } }
            else { Fl { pc: Pc::W0, wat: true, wr: s.d is Some, ..s } },
        Act::MergeOnly => read_merge(s),
        Act::Fail => Fl { pc: Pc::Idle, pend: true, ..s },
        // the displacement is done and the disk holds the write (fix ec2eff8: the record is updated
        // before `persist`); the handler returns the error and the write stays pending
        Act::FailSave => { let t = w3(s); Fl { pc: Pc::Idle, pend: true, ..t } },
        Act::Retry => if s.c is None { Fl { pend: false, ..remove_or_merge(s) } }
            else { Fl { pc: Pc::W0, wat: false, wr: true, ..s } },
        // `retry_removals` (also reached from `finish_git`): the file stays on disk, the shared
        // document no longer has it, the record is kept so only a changed file counts as outside
        Act::FailRemove => Fl { c: None, pend: true, ..s },
        Act::Own(b) => if b { Fl { own: true, ..s } }
            else if s.git { Fl { own: false, pend: true, ..s } }
            else { Fl { own: false, pc: Pc::W0, wat: false, wr: true, ..s } },
        Act::GitStart => Fl { git: true, ..s },
        // deferred removals, then rescan, then deferred writes
        Act::GitFinish => {
            let s1 = if s.c is None { remove_or_merge(s) } else { s };
            Fl { git: false, pc: Pc::W0, wat: false, wr: s.pend, ..s1 }
        },
        Act::Step => match s.pc {
            Pc::W0 => {
                let n2 = if s.wat && s.n > 0 { (s.n - 1) as nat } else { s.n };
                let r = read_merge(s);
                Fl { pc: if s.wr { Pc::W1 } else { Pc::Idle }, n: n2, wat: false, ..r }
            }
            Pc::W1 => match s.c {
                None => Fl { pc: Pc::Idle, pend: s.pend && (s.d is Some || s.dc is Some), ..s },
                Some(x) => Fl { pc: Pc::W2, lc: x, ..s },
            },
            Pc::W2 => if s.d == Some(s.lc) { Fl { pc: Pc::W4, dc: Some(s.lc), ..s } }
                else { Fl { pc: Pc::W3, ..s } },
            // `replace_file_keeping` + merge of the displaced bytes (`ensure_file_has_bytes`)
            Pc::W3 => w3(s),
            Pc::W4 => if s.c == Some(s.lc) { Fl { pc: Pc::Idle, pend: false, ..s } }
                else { Fl { pc: Pc::W1, ..s } },
            Pc::Idle => s,
        },
    }
}

pub open spec fn inv(s: Fl) -> bool {
    &&& (!(s.pc is Idle) ==> !s.git)
    // every outside change is covered by a queued event; the exception is the file deleted on disk
    // while an editor has it open (shared text becomes empty, the disk file stays absent)
    &&& ((!s.git && !(s.pc is W0) && s.n == 0) ==>
            (s.dc == s.d || (s.own && s.d is None && s.dc is Some)))
    &&& ((s.pc is Idle && !s.pend) ==> s.dc == s.c)
    &&& ((s.pc is W0 && !s.wr && !s.pend) ==> s.dc == s.c)
    &&& (s.pc is W4 ==> s.dc == Some(s.lc))
    &&& (s.own ==> s.c is Some)
    &&& ((s.c is None && !s.git && !s.pend) ==> s.dc is None)
    &&& (((s.pc is W2) || (s.pc is W3) || (s.pc is W4)) ==> s.c is Some)
    &&& !s.lost
}

pub proof fn lemma_step(s: Fl, a: Act)
    requires inv(s), enabled(s, a),
    ensures inv(step(s, a)),
{
    if a is MergeOnly || a is Step || a is GitFinish {
        match s.c { Some(x) => {}, None => {} }
        if s.dc is Some { axiom_merge_clean(s.dc->Some_0, empty_t()); }
        if s.dc is Some && s.d is Some { axiom_merge_clean(s.dc->Some_0, s.d->Some_0); }
    }
}

// Quiescence: no handler running, no deferral, no queued event => the file is the shared text,
// except an owned file deleted on disk (kept in the shared document as the empty text).
pub proof fn theorem_idle_agreement(s: Fl)
    requires inv(s), s.pc is Idle, !s.pend, !s.git, s.n == 0,
    ensures s.d == s.c || (s.own && s.d is None),
{}

pub proof fn lemma_init(t: int)
    ensures inv(Fl { pc: Pc::Idle, c: Some(t), dc: Some(t), d: Some(t), n: 0, lc: t, wat: false, wr: false, pend: false, own: false, git: false, lost: false }),
{}

// Non-vacuity: an editor opens the file, the file is deleted on disk, the watcher event is handled:
// the shared text becomes empty and the disk file stays absent; closing the editor then deletes it
// from the shared document.
pub proof fn example_owned_deletion(t: int)
    ensures ({
        let s0 = Fl { pc: Pc::Idle, c: Some(t), dc: Some(t), d: Some(t), n: 0, lc: t, wat: false, wr: false, pend: false, own: false, git: false, lost: false };
        let s1 = step(s0, Act::Own(true));
        let s2 = step(s1, Act::Outside(None));
        let s3 = step(s2, Act::Watch);
        let s4 = step(s3, Act::Step);            // W0 (Removed event: no write)
        let s5 = step(s4, Act::Own(false));      // editor closes: release_files
        let s6 = step(s5, Act::Step);            // W0: file gone, nobody owns it
        let s7 = step(s6, Act::Step);            // W1: not in the CRDT: nothing to write
        s4.pc is Idle && s4.c == Some(empty_t()) && s4.d is None && s4.own
        && s7.pc is Idle && s7.c is None && s7.dc is None
    }),
{
    axiom_merge_clean(t, empty_t());
}

} // verus!
fn main() {}
