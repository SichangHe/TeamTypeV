// Crash-consistency model of one shared file: persisted document, disk file, pending record.
// Source modeled: daemon.rs persist, mark_pending, unmark_pending, try_write_file,
// ensure_file_has_bytes, apply_pending_writes, git deferral (git_running), spawn_persister.
use vstd::prelude::*;
verus! {

type V = Option<nat>; // file content; None = file missing

#[derive(PartialEq, Eq)]
pub enum Pc { Idle, Recvd, Marked, Scanned, Persisted, Written, Skipped, Rebased }

pub struct S {
    pub d: V,                // in-memory document value (volatile)
    pub pd: V,               // persisted document (.teamtypev/doc)
    pub disk: V,             // the shared file on disk
    pub pend: Option<V>,     // pending-writes record: Some(base)
    pub agreed: V,           // disk_content (volatile)
    pub ahead: bool,         // ghost: the disk holds a document state newer than pd (skipped write)
    pub fo: bool,            // ghost: disk was last written by an outside actor (or Git)
    pub git: bool,           // git_running (volatile)
    pub pc: Pc,              // position inside the single actor handler (volatile)
}

pub uninterp spec fn merge(base: V, shared: V, outside: V) -> V; // OT three-way merge: trusted, opaque

pub enum Step { Recv(V), Mark, Rebase, MergeSave(V), NoWrite, UnmarkS, Defer, ScanW(V), PersistW, WriteW, UnmarkW, Persister,
    Outside(V), ScanI(V), Retry, GitStart, GitFinish }

pub open spec fn next(s: S, st: Step, t: S) -> bool {
    match st {
        Step::Recv(v) => s.pc == Pc::Idle && t == S { d: v, pc: Pc::Recvd, ..s },
        // mark_pending: record the base unless a record exists (`or_insert`)
        Step::Mark => s.pc == Pc::Recvd && t == S {
            pend: if s.pend is Some { s.pend } else { Some(s.agreed) }, pc: Pc::Marked, ..s },
        // write_file while Git runs: deferred
        Step::Defer => s.pc == Pc::Marked && s.git && t == S { pc: Pc::Idle, ..s },
        // try_write_file starts with file_created_or_changed (reads disk, merges); w = merge result
        Step::ScanW(w) => s.pc == Pc::Marked && !s.git
            && t == S { agreed: s.disk, d: if s.disk == s.agreed { s.d } else { w }, pc: Pc::Scanned, ..s },
        // ensure_file_has_bytes: persist() before replace_file
        Step::PersistW => s.pc == Pc::Scanned && t == S { pd: s.d, ahead: false, pc: Pc::Persisted, ..s },
        // replace_file (atomic); the disk is what the scan just read
        Step::WriteW => s.pc == Pc::Persisted && s.disk == s.agreed
            && t == S { disk: s.d, agreed: s.d, fo: false, ahead: false, pc: Pc::Written, ..s },
        // ensure_file_has_bytes returns early when the disk already has the bytes: persists (after b-fix), no write
        Step::NoWrite => s.pc == Pc::Scanned && s.disk == s.d && t == S { pd: s.d, pc: Pc::Skipped, ..s },
        Step::UnmarkS => s.pc == Pc::Skipped && t == S { pend: None, pc: Pc::Idle, ..s },
        // ensure_file_has_bytes found displaced (outside) bytes: first the record's base becomes what the
        // disk now holds (`rebase_pending`), then the merge is applied and saved (`persist`)
        Step::Rebase => s.pc == Pc::Written && t == S { pend: Some(s.disk), pc: Pc::Rebased, ..s },
        Step::MergeSave(w) => s.pc == Pc::Rebased && t == S { d: w, pd: w, pc: Pc::Scanned, ..s },
        Step::UnmarkW => s.pc == Pc::Written && t == S { pend: None, pc: Pc::Idle, ..s },
        // DocMessage::Persist (the actor handles messages one at a time)
        Step::Persister => s.pc == Pc::Idle && t == S { pd: s.d, ahead: false, ..s },
        // editor-less outside write or Git; only between handlers
        Step::Outside(w) => s.pc == Pc::Idle && t == S { disk: w, fo: true, ..s },
        // watcher/rescan/finish_git: file_created_or_changed
        Step::ScanI(w) => s.pc == Pc::Idle && !s.git && t == S {
            agreed: s.disk,
            d: if s.disk == s.agreed { s.d } else if s.pend is None { s.disk } else { w },
            ..s },
        // finish_git re-runs deferred writes
        Step::Retry => s.pc == Pc::Idle && !s.git && s.pend is Some && t == S { pc: Pc::Marked, ..s },
        Step::GitStart => s.pc == Pc::Idle && !s.git && t == S { git: true, ..s },
        Step::GitFinish => s.pc == Pc::Idle && s.git && t == S { git: false, ..s },
    }
}

pub open spec fn inv(s: S) -> bool {
    // A: the daemon's belief about the disk is right unless an outside actor wrote it
    &&& (s.agreed == s.disk || s.fo)
    // B: with no record, between handlers the document equals what it last agreed with the disk
    &&& (s.pc == Pc::Idle && s.pend is None ==> s.d == s.agreed)
    // C: without outside writes the disk is never ahead of or unrelated to the persisted document,
    //    except that a record holds exactly the disk's content
    &&& (!s.fo && s.pend is Some ==> (s.disk == s.pd || s.pend->Some_0 == s.disk))
    &&& (!s.fo && s.pend is None ==> s.disk == s.pd)
    &&& (s.pc == Pc::Skipped ==> s.disk == s.d && s.agreed == s.d && s.pd == s.d)
    // D: inside a write the record exists and (without outside writes) holds the disk's content
    &&& ((s.pc == Pc::Marked || s.pc == Pc::Scanned || s.pc == Pc::Persisted || s.pc == Pc::Skipped) ==>
            (s.pend is Some && (!s.fo ==> s.pend->Some_0 == s.disk)))
    // E: between handlers a record is exact unless an outside actor wrote the disk
    &&& (s.pc == Pc::Idle && s.pend is Some ==> (s.pend->Some_0 == s.disk || s.fo))
    // E': the same right after a peer's change arrived
    &&& (s.pc == Pc::Recvd && s.pend is Some ==> (s.pend->Some_0 == s.disk || s.fo))
    // I: Git cannot start inside a handler, so a write in progress never overlaps Git
    &&& ((s.pc == Pc::Scanned || s.pc == Pc::Persisted || s.pc == Pc::Written || s.pc == Pc::Skipped) ==> !s.git)
    // K: after the scan the belief is exact
    &&& ((s.pc == Pc::Scanned || s.pc == Pc::Persisted) ==> s.agreed == s.disk)
    // R: after the displaced bytes were found, the record holds exactly the disk's bytes
    &&& (s.pc == Pc::Rebased ==> s.pend is Some && s.pend->Some_0 == s.disk && s.pd == s.disk && s.agreed == s.disk && !s.git)
    // F: persisted before written
    &&& (s.pc == Pc::Persisted ==> s.pd == s.d)
    &&& (s.pc == Pc::Written ==> s.pd == s.d && s.disk == s.d && s.agreed == s.d)
}

pub open spec fn init(s: S) -> bool {
    s.pd == s.disk && s.d == s.disk && s.agreed == s.disk && s.pend is None && !s.ahead && !s.fo && !s.git && s.pc == Pc::Idle
}

// Restart after a kill at any point: volatile state is lost; apply_pending_writes + the scan.
pub open spec fn restart(s: S) -> S {
    match s.pend {
        None => S { d: s.disk, agreed: s.disk, git: false, ahead: false, pc: Pc::Idle, ..s },
        Some(b) =>
            if s.disk == s.pd { S { d: s.pd, pend: None, agreed: s.disk, git: false, pc: Pc::Idle, ..s } }
            else if s.disk == b { S { d: s.pd, agreed: s.disk, git: false, pc: Pc::Idle, ..s } }
            else { S { d: merge(b, s.pd, s.disk), agreed: s.disk, git: false, pc: Pc::Idle, ..s } },
    }
}

// Git isolation: while Git runs, the daemon changes neither the disk nor the document file;
// only an outside actor (Git itself) changes the disk.
proof fn theorem_git_isolation(s: S, st: Step, t: S)
    requires inv(s), s.git, next(s, st, t),
    ensures t.disk != s.disk ==> st is Outside, t.pd != s.pd ==> st is Persister || st is PersistW,
        st is WriteW ==> false,
{}

proof fn lemma_init(s: S) requires init(s) ensures inv(s) {}

proof fn lemma_step(s: S, st: Step, t: S) requires inv(s), next(s, st, t) ensures inv(t) {
    match st {
        Step::NoWrite => {}
        Step::UnmarkS => {}
        Step::Recv(v) => {}
        Step::Mark => {}
        Step::Defer => {}
        Step::ScanW(w) => {}
        Step::PersistW => {}
        Step::WriteW => {}
        Step::Rebase => {}
        Step::MergeSave(w) => {}
        Step::UnmarkW => {}
        Step::Persister => {}
        Step::Outside(w) => {}
        Step::ScanI(w) => {}
        Step::Retry => {}
        Step::GitStart => {}
        Step::GitFinish => {}
    }
}

// Killed at any reachable point, then restarted: no outside write => the document is exactly the
// persisted one (no reverted peer edit, no duplicate), and the restarted state is again invariant.
proof fn theorem_restart(s: S)
    requires inv(s),
    ensures
        inv(restart(s)),
        !s.fo ==> restart(s).d == s.pd,
        (s.fo && s.pend is None) ==> restart(s).d == s.disk,
{}

// Non-vacuity: the dangerous interleaving is reachable (killed after the write, before clearing the
// record: disk == persisted document, record base differs) and the restart case handles it.
proof fn witness_trace() {
    let s0 = S { d: Some(1nat), pd: Some(1nat), disk: Some(1nat), pend: None, agreed: Some(1nat), fo: false, ahead: false, git: false, pc: Pc::Idle };
    let s1 = S { d: Some(2nat), pc: Pc::Recvd, ..s0 };
    let s2 = S { pend: Some(Some(1nat)), pc: Pc::Marked, ..s1 };
    let s3 = S { pc: Pc::Scanned, ..s2 };
    let s4 = S { pd: Some(2nat), pc: Pc::Persisted, ..s3 };
    let s5 = S { disk: Some(2nat), agreed: Some(2nat), pc: Pc::Written, ..s4 };
    assert(init(s0));
    assert(next(s0, Step::Recv(Some(2nat)), s1));
    assert(next(s1, Step::Mark, s2));
    assert(next(s2, Step::ScanW(None), s3));
    assert(next(s3, Step::PersistW, s4));
    assert(next(s4, Step::WriteW, s5));
    assert(inv(s5));
    // killed here: record base 1, disk 2 == persisted 2
    assert(s5.pend == Some(Some(1nat)) && s5.disk == s5.pd && s5.pend->Some_0 != s5.disk);
    assert(restart(s5).d == Some(2nat) && restart(s5).pend is None);
}

// ---- Restart recovery decision: the real code's pure core, checked against `restart`. ----
// corr: crates/teamtype/src/daemon.rs :: enum PendingRecovery
/// What restart recovery does with one pending-write record (`apply_pending_writes`).
#[derive(Debug, PartialEq, Eq)]
enum PendingRecovery {
    /// The disk already holds the document's bytes: only clear the record.
    Finished,
    /// Merge the disk's bytes against the record's base, then write the result.
    MergeThenWrite,
    /// Peers deleted the file but it changed on disk: drop the record, the rescan shares the edit.
    KeepOutsideEdit,
    /// Write the document's file, or remove the disk file if the document has none.
    Write,
}
// corr-end

// corr: crates/teamtype/src/daemon.rs :: pending_recovery
/// Pure decision of `apply_pending_writes`, mirrored by `restart` in the crash-consistency proof.
#[expect(clippy::fn_params_excessive_bools)]
fn pending_recovery(
    on_disk: bool,
    in_document: bool,
    disk_matches_document: bool,
    disk_matches_base: bool,
) -> (r: PendingRecovery)
    ensures
        (r == PendingRecovery::Finished) == (on_disk && in_document && disk_matches_document),
        (r == PendingRecovery::MergeThenWrite) == (on_disk && in_document && !disk_matches_document),
        (r == PendingRecovery::KeepOutsideEdit) == (on_disk && !in_document && !disk_matches_base),
        (r == PendingRecovery::Write) == (!on_disk || (!in_document && disk_matches_base)),
{
    if on_disk && in_document && disk_matches_document {
        PendingRecovery::Finished
    } else if on_disk && in_document {
        PendingRecovery::MergeThenWrite
    } else if on_disk && !disk_matches_base {
        PendingRecovery::KeepOutsideEdit
    } else {
        PendingRecovery::Write
    }
}
// corr-end

/// The real decision on a model state after a kill: the document is the persisted one (`pd`),
/// `None` means missing. Result of `pending_recovery` with these flags.
spec fn recovery_flags_hold(s: S, r: PendingRecovery) -> bool {
    let on_disk = s.disk is Some;
    let in_document = s.pd is Some;
    let mdoc = on_disk && in_document && s.disk == s.pd;
    let mbase = on_disk && s.pend->Some_0 == s.disk;
    &&& (r == PendingRecovery::Finished) == (on_disk && in_document && mdoc)
    &&& (r == PendingRecovery::MergeThenWrite) == (on_disk && in_document && !mdoc)
    &&& (r == PendingRecovery::KeepOutsideEdit) == (on_disk && !in_document && !mbase)
    &&& (r == PendingRecovery::Write) == (!on_disk || (!in_document && mbase))
}

/// The real decision agrees with `restart` on every pending record: it clears the record exactly
/// where `restart` does (or removes an already-missing file), keeps the persisted document unless
/// the disk diverged from the record's base, and only merges where `restart` merges or the merge
/// is with base == disk (identity in the real OT merge; trusted, `merge` is opaque here).
proof fn lemma_recovery_matches_restart(s: S, r: PendingRecovery)
    requires s.pend is Some, recovery_flags_hold(s, r),
    ensures
        r == PendingRecovery::Finished ==> restart(s).pend is None && restart(s).d == s.pd,
        restart(s).pend is None ==> r == PendingRecovery::Finished
            || (r == PendingRecovery::Write && s.disk is None && s.pd is None),
        r == PendingRecovery::MergeThenWrite ==> s.disk != s.pd
            && (restart(s).d == s.pd || restart(s).d == merge(s.pend->Some_0, s.pd, s.disk)),
        r == PendingRecovery::MergeThenWrite && s.disk == s.pend->Some_0 ==> restart(s).d == s.pd,
        // Write with the file missing on disk: `restart` merges the deletion (`merge(b, pd, None)`);
        // the real code defers that to the scan at the start of `try_write_file` (not modeled here).
        r == PendingRecovery::Write ==> restart(s).d == s.pd || s.disk is None,
        r == PendingRecovery::KeepOutsideEdit ==> s.pd is None && s.disk is Some
            && restart(s).d == merge(s.pend->Some_0, s.pd, s.disk),
{}

/// Non-vacuity: every outcome of the decision is reachable from some model state.
proof fn witness_recovery() {
    let base = S { d: None, pd: Some(1), disk: Some(1), pend: Some(Some(0)), agreed: None,
        ahead: false, fo: false, git: false, pc: Pc::Idle };
    assert(recovery_flags_hold(base, PendingRecovery::Finished));
    let m = S { disk: Some(2), ..base };
    assert(recovery_flags_hold(m, PendingRecovery::MergeThenWrite));
    let k = S { pd: None, disk: Some(2), ..base };
    assert(recovery_flags_hold(k, PendingRecovery::KeepOutsideEdit));
    let w = S { disk: None, ..base };
    assert(recovery_flags_hold(w, PendingRecovery::Write));
}

} // verus!

fn main() {}
