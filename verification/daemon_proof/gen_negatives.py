# Regenerates negative/full_*.rs: each is disk_full.rs with one mutation that must be rejected.
import os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
s = open("disk_full.rs").read()
M = {
 "full_failed_write_not_pending": ("Act::Fail => Fl { pc: Pc::Idle, pend: true, ..s },", "Act::Fail => Fl { pc: Pc::Idle, pend: false, ..s },"),
 "full_git_sync_delete_not_pending": ("Act::SyncDelete => if s.git { Fl { c: None, pend: true, ..s } }", "Act::SyncDelete => if s.git { Fl { c: None, pend: false, ..s } }"),
 "full_outside_without_event": ("Act::Outside(t) => Fl { d: t, n: s.n + 1, ..s },", "Act::Outside(t) => Fl { d: t, n: s.n, ..s },"),
 "full_owned_removal_forgets_record": ("(Some(cur), Some(b)) => Fl { c: Some(merge(b, cur, empty_t())), dc: Some(empty_t()), ..s },", "(Some(cur), Some(b)) => Fl { c: Some(merge(b, cur, empty_t())), dc: None, ..s },"),
 "full_git_finish_keeps_removed_file_record": ("else { Fl { c: None, d: None, dc: None, lost: s.lost || displaced_unmerged(s), ..s } },", "else { Fl { c: None, d: None, lost: s.lost || displaced_unmerged(s), ..s } },"),
 "full_displaced_without_record_dropped": ("(Some(x), None) if x != empty_t() =>", "(Some(x), None) if false =>"),
 "full_sync_delete_without_disk_check": ("Some(x) => if s.dc != Some(x) {", "Some(x) => if false {"),
 "full_failed_remove_drops_record": ("Act::FailRemove => Fl { c: None, pend: true, ..s },", "Act::FailRemove => Fl { c: None, pend: true, dc: None, ..s },"),
 "full_failed_save_stale_record": ("Act::FailSave => { let t = w3(s); Fl { pc: Pc::Idle, pend: true, ..t } },", "Act::FailSave => { let t = w3(s); Fl { pc: Pc::Idle, pend: true, dc: s.dc, ..t } },"),
 "full_outside_replaces_shared_text": ("c: if s.c == Some(x) { s.c } else { Some(merge(empty_t(), s.lc, x)) }, d: Some(s.lc), dc: Some(s.lc), ..s },", "c: if s.c == Some(x) { s.c } else { Some(x) }, d: Some(s.lc), dc: Some(s.lc), repl: s.repl || s.c != Some(x), ..s },"),
 "full_merge_adopt_without_shortcut": ("(Some(cur), Some(_)) if cur == t => Fl { dc: Some(t), ..s },", ""),
}
for n, (a, b) in M.items():
    assert s.count(a) == 1, (n, s.count(a))
    open("negative/%s.rs" % n, "w").write(s.replace(a, b))
a = """        if s.dc is Some { axiom_merge_clean(s.dc->Some_0, empty_t()); }
        if s.dc is Some && s.d is Some { axiom_merge_clean(s.dc->Some_0, s.d->Some_0); }
"""
assert s.count(a) == 1
open("negative/full_merge_without_axiom.rs", "w").write(s.replace(a, ""))
