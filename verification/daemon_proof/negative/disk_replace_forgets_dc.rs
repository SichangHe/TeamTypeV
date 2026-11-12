// (authored by agents) NEGATIVE CONTROL: disk_replace_forgets_dc; Verus must reject it.
// (authored by agents) Verus model of daemon.rs's disk write routine (`try_write_file` /
// `ensure_file_has_bytes` / `merge_disk_content`) racing with outside writes (see DESIGN.md).
use vstd::prelude::*;

verus! {

// Texts are opaque ints: only equality matters. One file that exists throughout, and whose
// `disk_content` entry (`dc`) exists (removal, creation and the git deferral are not modeled).
pub uninterp spec fn merge(base: int, cur: int, outside: int) -> int; // dissimilar+OT merge, any result

// ASSUMED (dissimilar diff + OT transform): merging an outside text into an unchanged shared text
// gives the outside text. Needed for merge-only handlers.
#[verifier::external_body]
pub proof fn axiom_merge_clean(b: int, o: int)
    ensures merge(b, b, o) == o,
{}

pub enum Pc { Idle, W0, W1, W2, W3, W4 }

pub struct Dk {
    pub pc: Pc,
    pub c: int,    // CRDT text of the file (the cache equals it, see ../boundary_proof)
    pub dc: int,   // DocumentActor.disk_content[file]: last bytes read or written
    pub d: int,    // the real file on disk
    pub n: nat,    // watcher events queued but not yet handled
    pub lc: int,   // `content` snapshot taken by the `while let` loop of try_write_file
    pub wat: bool, // this handler run was started by a watcher event
    pub pend: bool, // a write failed (`deferred_writes`); a rescan retries it
}

pub enum Act {
    Outside(int),  // another process writes the file (and the OS queues a watcher event)
    CrdtChange(int), // a handler changes the CRDT text (sync, editor edit) and calls write_file
    Watch,         // actor takes a watcher event (`handle_watcher_event`)
    Step,          // actor executes the next step of the write routine
    MergeOnly,     // handler that only runs the merge step: Open/Edit pre-check, RescanFiles, GitHeads, remove_file of an owned file
    Fail,          // the write at W3 fails (persist or replace error): routine aborts, file marked pending
    Retry,         // RescanFiles retries a pending write
}

// ASSUMED: every outside write queues at least one watcher event that is handled later
// (inotify/FSEvents delivery; not proved).
pub open spec fn enabled(s: Dk, a: Act) -> bool {
    match a {
        Act::Outside(_) => true,
        Act::CrdtChange(_) => s.pc is Idle,
        Act::Watch => s.pc is Idle && s.n > 0,
        Act::Step => !(s.pc is Idle),
        Act::MergeOnly => s.pc is Idle,
        Act::Fail => s.pc is W3,
        Act::Retry => s.pc is Idle && s.pend,
    }
}

// Each Step is one read or write of the file system plus the actor's local updates; outside writes
// can land between any two Steps. `fixed` selects the early-return of `ensure_file_has_bytes`:
// the original code did not record the bytes it found equal (`fixed == false`).
pub open spec fn step(s: Dk, a: Act, fixed: bool) -> Dk {
    match a {
        Act::Outside(t) => Dk { d: t, n: s.n + 1, ..s },
        Act::CrdtChange(c2) => Dk { pc: Pc::W0, c: c2, wat: false, ..s },
        Act::MergeOnly => if s.d != s.dc { Dk { c: merge(s.dc, s.c, s.d), dc: s.d, ..s } } else { s },
        Act::Fail => Dk { pc: Pc::Idle, pend: true, ..s },
        Act::Retry => Dk { pc: Pc::W0, wat: false, ..s },
        Act::Watch => Dk { pc: Pc::W0, wat: true, ..s },
        Act::Step => match s.pc {
            // file_created_or_changed: read the disk; a difference from `dc` is merged into the CRDT
            Pc::W0 => {
                let n2 = if s.wat && s.n > 0 { (s.n - 1) as nat } else { s.n };
                if s.d != s.dc { Dk { pc: Pc::W1, c: merge(s.dc, s.c, s.d), dc: s.d, n: n2, wat: false, ..s } }
                else { Dk { pc: Pc::W1, n: n2, wat: false, ..s } }
            }
            Pc::W1 => Dk { pc: Pc::W2, lc: s.c, ..s },
            // ensure_file_has_bytes: read the disk and compare
            Pc::W2 => if s.d == s.lc {
                Dk { pc: Pc::W4, dc: if fixed { s.lc } else { s.dc }, ..s }
            } else { Dk { pc: Pc::W3, ..s } },
            // replace_file returns the displaced bytes, merged if they are not the known ones;
            // then `disk_content` records what was written
            Pc::W3 => if s.d != s.dc {
                Dk { pc: Pc::W4, c: merge(s.dc, s.c, s.d), d: s.lc, dc: s.lc, ..s }
            } else { Dk { pc: Pc::W4, d: s.lc, ..s } },
            // loop condition: the CRDT moved while writing (a merge): write again
            Pc::W4 => if s.c == s.lc { Dk { pc: Pc::Idle, pend: false, ..s } } else { Dk { pc: Pc::W1, ..s } },
            Pc::Idle => s,
        },
    }
}

// Every outside change is covered by a queued event, and between handlers the daemon's cache of
// the disk equals the shared text.
pub open spec fn inv(s: Dk) -> bool {
    &&& (s.n == 0 ==> s.dc == s.d)
    &&& (s.pc is Idle && !s.pend ==> s.dc == s.c)
    &&& (s.pc is W4 ==> s.dc == s.lc)
}

pub proof fn lemma_step(s: Dk, a: Act)
    requires inv(s), enabled(s, a),
    ensures inv(step(s, a, true)),
{
    if a is MergeOnly { axiom_merge_clean(s.dc, s.d); }
}

// Between handlers with no queued event, the file is exactly the shared text.
pub proof fn theorem_idle_agreement(s: Dk)
    requires inv(s), s.pc is Idle, !s.pend, s.n == 0,
    ensures s.d == s.c,
{}

// The state a daemon is in after scanning the directory: nothing queued, all equal.
pub proof fn lemma_init(t: int)
    ensures inv(Dk { pc: Pc::Idle, c: t, dc: t, d: t, n: 0, lc: t, wat: false, pend: false }),
{}

// Non-vacuity: the interleaving that needed the fix. A peer's change (c = 2) arrives, then an outside
// process writes the very same text before the actor reads the disk again.
pub proof fn example_coincident_write()
    ensures ({
        let s0 = Dk { pc: Pc::Idle, c: 1, dc: 1, d: 1, n: 0, lc: 1, wat: false, pend: false };
        let s1 = step(s0, Act::CrdtChange(2), true);
        let s2 = step(s1, Act::Step, true);      // W0: disk is still 1: nothing to merge
        let s3 = step(s2, Act::Step, true);      // W1
        let s4 = step(s3, Act::Outside(2), true); // outside write: disk is now 2
        let s5 = step(s4, Act::Step, true);      // W2: disk == content, early return
        let s6 = step(s5, Act::Step, true);      // W4
        s6.pc is Idle && s6.dc == 2 && s6.d == 2 && s6.c == 2 && s6.n == 1
    }),
{
    lemma_init(1);
}

} // verus!
fn main() {}
