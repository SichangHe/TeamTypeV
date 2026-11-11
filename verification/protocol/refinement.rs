// Verus refinement of teamtype `OTServer` (source/ot.rs): the revision state
// machine and server-side convergence of the real method bodies.
// Exec bodies of `apply_crdt_change`, `apply_editor_operation`,
// `deltas_for_editor`, `transform_through_operations` are the source bodies
// with only the rewrites listed in REFINEMENT.md / refinement_source.diff.
// The operational-transform crate, text conversions and `force_apply` are
// trusted via external_body specs and the axioms below (ASSUMED).
use vstd::prelude::*;

verus! {

// ---------- trusted model (ASSUMED) ----------
// An operation is an opaque value; `ap(d, o)` is the text after applying o to d
// (what `force_apply` computes, including its padding).
pub uninterp spec fn ap(d: Seq<char>, o: int) -> Seq<char>;
// `m.transform(t)` = (m', t'); `pad(o, n)` = o after `retain(n)`.
pub uninterp spec fn tr_my(m: int, t: int) -> int;
pub uninterp spec fn tr_their(m: int, t: int) -> int;
pub uninterp spec fn pad(o: int, n: nat) -> int;
pub uninterp spec fn base_len_of(o: int) -> nat;

// TP1: m then t' == t then m'
#[verifier::external_body]
pub proof fn axiom_tp1(d: Seq<char>, m: int, t: int)
    ensures ap(ap(d, m), tr_their(m, t)) == ap(ap(d, t), tr_my(m, t)),
{}

// trailing retain does not change the result of force_apply
#[verifier::external_body]
pub proof fn axiom_pad(d: Seq<char>, o: int, n: nat)
    ensures ap(d, pad(o, n)) == ap(d, o),
{}

pub open spec fn fold(d: Seq<char>, q: Seq<int>) -> Seq<char>
    decreases q.len(),
{
    if q.len() == 0 { d } else { fold(ap(d, q[0]), q.drop_first()) }
}

proof fn lemma_fold_snoc(d: Seq<char>, q: Seq<int>, x: int)
    ensures fold(d, q.push(x)) == ap(fold(d, q), x),
    decreases q.len(),
{
    if q.len() == 0 {
        assert(q.push(x).drop_first() =~= Seq::<int>::empty());
        assert(q.push(x)[0] == x);
        assert(fold(d, q.push(x)) == fold(ap(d, x), q.push(x).drop_first()));
    } else {
        assert(q.push(x).drop_first() =~= q.drop_first().push(x));
        assert(q.push(x)[0] == q[0]);
        assert(fold(d, q) == fold(ap(d, q[0]), q.drop_first()));
        assert(fold(d, q.push(x)) == fold(ap(d, q[0]), q.push(x).drop_first()));
        lemma_fold_snoc(ap(d, q[0]), q.drop_first(), x);
    }
}

proof fn lemma_fold_split(d: Seq<char>, q: Seq<int>, k: int)
    requires 0 <= k <= q.len(),
    ensures fold(d, q) == fold(fold(d, q.subrange(0, k)), q.subrange(k, q.len() as int)),
    decreases k,
{
    if k == 0 {
        assert(q.subrange(0, 0) =~= Seq::<int>::empty());
        assert(q.subrange(0, q.len() as int) =~= q);
    } else {
        assert(q.subrange(0, k) =~= q.subrange(0, k - 1).push(q[k - 1]));
        lemma_fold_snoc(d, q.subrange(0, k - 1), q[k - 1]);
        lemma_fold_split(d, q, k - 1);
        let r = q.subrange(k - 1, q.len() as int);
        assert(r.drop_first() =~= q.subrange(k, q.len() as int));
    }
}

#[verifier::external_body]
pub struct OperationSeq { inner: () }
impl OperationSeq {
    pub uninterp spec fn view(&self) -> int;

    #[verifier::external_body]
    pub fn clone(&self) -> (r: Self) ensures r@ == self@ { unimplemented!() }
    #[verifier::external_body]
    pub fn base_len(&self) -> (r: usize) ensures r == base_len_of(self@) { unimplemented!() }
    #[verifier::external_body]
    pub fn retain(&mut self, n: u64) ensures final(self)@ == pad(old(self)@, n as nat) { unimplemented!() }
    // the source's `.transform(..).unwrap_or_else(|_| panic!(..))`; trusted not to fail
    #[verifier::external_body]
    pub fn transform_or_panic(&self, other: &OperationSeq) -> (r: (OperationSeq, OperationSeq))
        ensures r.0@ == tr_my(self@, other@), r.1@ == tr_their(self@, other@),
    { unimplemented!() }
}

pub struct Error;
pub type Result<T> = core::result::Result<T, Error>;

#[verifier::external_body]
pub struct TextDelta { inner: () }
#[verifier::external_body]
pub struct EditorTextDelta { inner: () }
pub uninterp spec fn delta_op(d: TextDelta) -> int;
pub uninterp spec fn op_delta(o: int) -> TextDelta;
impl TextDelta {
    #[verifier::external_body]
    pub fn clone(&self) -> (r: Self) ensures r == *self { unimplemented!() }
}
// `.into()` conversions
#[verifier::external_body]
pub fn op_from_delta(d: TextDelta) -> (r: OperationSeq) ensures r@ == delta_op(d) { unimplemented!() }
#[verifier::external_body]
pub fn delta_from_op(o: OperationSeq) -> (r: TextDelta) ensures r == op_delta(o@) { unimplemented!() }
#[verifier::external_body]
pub fn try_from_delta(d: TextDelta, content: &str) -> (r: Result<EditorTextDelta>) { unimplemented!() }
// `EditorTextDelta::try_from_delta(..).expect(..)` in deltas_for_editor; trusted not to fail
#[verifier::external_body]
pub fn try_from_delta_expect(d: TextDelta, content: &str) -> (r: EditorTextDelta) { unimplemented!() }

pub struct RevisionedEditorTextDelta { pub revision: usize, pub delta: EditorTextDelta }
pub struct RevisionedTextDelta { pub revision: usize, pub delta: TextDelta }
#[verifier::external_body]
pub fn try_from_rev_ed_delta(r: RevisionedEditorTextDelta, content: &str) -> (o: Result<RevisionedTextDelta>)
{ unimplemented!() }

// `Vec::drain(..n)` collected
#[verifier::external_body]
pub fn drain_front(v: &mut Vec<OperationSeq>, n: usize) -> (r: Vec<OperationSeq>)
    requires n <= old(v)@.len(),
    ensures
        r@.map_values(|o: OperationSeq| o@) == old(v)@.map_values(|o: OperationSeq| o@).subrange(0, n as int),
        final(v)@.map_values(|o: OperationSeq| o@) == old(v)@.map_values(|o: OperationSeq| o@).subrange(n as int, old(v)@.len() as int),
{ unimplemented!() }

// source `force_apply`; body uses the library `apply`, trusted not to panic
#[verifier::external_body]
fn force_apply(document: &str, op_seq: OperationSeq) -> (r: String)
    ensures r@ == ap(document@, op_seq@),
{ unimplemented!() }

// `assert!(c, msg)`: reachable only if Verus can prove it is never called
fn panic_assert()
    requires false,
{}

pub open spec fn ops(v: Seq<OperationSeq>) -> Seq<int> { v.map_values(|o: OperationSeq| o@) }

// ---------- the real code ----------
pub struct OTServer {
    pub editor_revision: usize,
    pub daemon_revision: usize,
    pub operations: Vec<OperationSeq>,
    pub editor_queue: Vec<OperationSeq>,
    pub current_content: String,
    pub last_confirmed_editor_content: String,
}

impl OTServer {
    // revision state machine invariant + server-side convergence:
    // the editor's confirmed text, after the unacknowledged daemon ops, is the daemon text
    pub open spec fn wf(&self) -> bool {
        &&& self.editor_queue@.len() <= self.daemon_revision
        &&& fold(self.last_confirmed_editor_content@, ops(self.editor_queue@)) == self.current_content@
    }

    // corr: crates/teamtype/src/ot.rs :: OTServer::new
    pub fn new(initial_content: String) -> (r: Self)
        ensures r.wf(), r.editor_revision == 0, r.daemon_revision == 0,
    {
        Self {
            last_confirmed_editor_content: initial_content.clone(),
            current_content: initial_content,
            editor_revision: 0, daemon_revision: 0,
            operations: Vec::new(), editor_queue: Vec::new(),
        }
    }
    // corr-end

    // corr: crates/teamtype/src/ot.rs :: OTServer::apply_crdt_change
    pub fn apply_crdt_change(&mut self, delta: &TextDelta) -> (r: Result<RevisionedEditorTextDelta>)
        requires old(self).wf(), old(self).daemon_revision < usize::MAX,
        ensures
            // state advances even on Err
            final(self).daemon_revision == old(self).daemon_revision + 1,
            final(self).editor_revision == old(self).editor_revision,
            ops(final(self).editor_queue@) == ops(old(self).editor_queue@).push(delta_op(*delta)),
            r is Ok ==> final(self).wf() && r->Ok_0.revision == old(self).editor_revision
                && final(self).current_content@ == ap(old(self).current_content@, delta_op(*delta)),
    {
        // We can apply the change immediately.
        self.operations.push(op_from_delta(delta.clone()));
        self.editor_queue.push(op_from_delta(delta.clone()));
        self.daemon_revision += 1;
        // Use "previous" content to transform into editor text delta.
        let editor_delta = match try_from_delta(delta.clone(), self.current_content.as_str()) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        self.current_content = force_apply(self.current_content.as_str(), op_from_delta(delta.clone()));
        proof {
            assert(ops(self.editor_queue@) =~= ops(old(self).editor_queue@).push(delta_op(*delta)));
            lemma_fold_snoc(self.last_confirmed_editor_content@, ops(old(self).editor_queue@), delta_op(*delta));
        }

        // We assume that the editor is up-to-date, and send the operation to it.
        // If it can't accept it, we will transform and send it later.
        Ok(RevisionedEditorTextDelta {
            revision: self.editor_revision,
            delta: editor_delta,
        })
    }
    // corr-end

    pub fn apply_editor_operation(
        &mut self,
        rev_editor_delta: RevisionedEditorTextDelta,
    ) -> (r: Result<(TextDelta, Vec<RevisionedEditorTextDelta>)>)
        requires
            old(self).wf(), old(self).editor_revision < usize::MAX,
            // precondition for no panic (the two asserts)
            rev_editor_delta.revision <= old(self).daemon_revision,
            old(self).daemon_revision - rev_editor_delta.revision <= old(self).editor_queue@.len(),
        ensures
            // editor revision advances even on Err
            final(self).editor_revision == old(self).editor_revision + 1,
            final(self).daemon_revision == old(self).daemon_revision,
            r is Ok ==> {
                &&& final(self).wf()
                &&& final(self).editor_queue@.len() == old(self).daemon_revision - rev_editor_delta.revision
                &&& r->Ok_0.1@.len() == final(self).editor_queue@.len()
                &&& forall|i: int| 0 <= i < r->Ok_0.1@.len() ==> r->Ok_0.1@[i].revision == final(self).editor_revision
                &&& exists|o: int| r->Ok_0.0 == op_delta(o) && final(self).current_content@ == ap(old(self).current_content@, o)
            },
    {
        let daemon_revision = rev_editor_delta.revision;
        self.editor_revision += 1;

        let mut op_seq: OperationSeq;

        if !(daemon_revision <= self.daemon_revision) { panic_assert(); }
        // "This must not happen, editor has seen a daemon revision from the future."

        let daemon_operations_to_transform = self.daemon_revision - daemon_revision;
        if !(self.editor_queue.len() >= daemon_operations_to_transform) { panic_assert(); }
        // "Whoopsie, we don't have enough operations cached. Was this already processed?"
        let seen_operations = self.editor_queue.len() - daemon_operations_to_transform;
        let ghost q0 = ops(self.editor_queue@);
        let ghost l0 = self.last_confirmed_editor_content@;
        let confirmed_queue = drain_front(&mut self.editor_queue, seen_operations);
        assert(ops(confirmed_queue@) == q0.subrange(0, seen_operations as int));
        assert(confirmed_queue@.len() == ops(confirmed_queue@).len());
        let mut i: usize = 0;
        while i < confirmed_queue.len()
            invariant
                i <= confirmed_queue@.len(),
                seen_operations <= q0.len(),
                confirmed_queue@.len() == seen_operations,
                ops(confirmed_queue@) == q0.subrange(0, seen_operations as int),
                self.last_confirmed_editor_content@ == fold(l0, q0.subrange(0, i as int)),
            decreases confirmed_queue@.len() - i,
        {
            let confirmed_editor_op = &confirmed_queue[i];
            proof {
                assert(q0.subrange(0, i + 1) =~= q0.subrange(0, i as int).push(ops(confirmed_queue@)[i as int]));
                lemma_fold_snoc(l0, q0.subrange(0, i as int), ops(confirmed_queue@)[i as int]);
            }
            self.last_confirmed_editor_content = force_apply(
                self.last_confirmed_editor_content.as_str(),
                confirmed_editor_op.clone(),
            );
            i += 1;
        }
        proof { lemma_fold_split(l0, q0, seen_operations as int); }
        let rev_delta = match try_from_rev_ed_delta(
            rev_editor_delta,
            self.last_confirmed_editor_content.as_str(),
        ) {
            Ok(x) => x,
            Err(e) => return Err(e),
        };
        op_seq = op_from_delta(rev_delta.delta);

        let ghost l1 = self.last_confirmed_editor_content@;
        let ghost e = op_seq@;
        self.last_confirmed_editor_content =
            force_apply(self.last_confirmed_editor_content.as_str(), op_seq.clone());
        let (op_seq2, q2) = transform_through_operations(op_seq, &self.editor_queue);
        proof { transform_spec_inst(l1, e, ops(self.editor_queue@), op_seq2@, ops(q2@)); }
        proof {
            let u = ops(self.editor_queue@);
            assert(u =~= q0.subrange(seen_operations as int, q0.len() as int));
            assert(self.current_content@ == fold(l1, u));
        }
        op_seq = op_seq2;
        self.editor_queue = q2;
        self.operations.push(op_seq.clone());
        self.current_content = force_apply(self.current_content.as_str(), op_seq.clone());

        let deltas_for_editor = self.deltas_for_editor();
        assert(ops(self.editor_queue@).len() == self.editor_queue@.len());
        assert(self.wf());

        Ok((delta_from_op(op_seq), deltas_for_editor))
    }

    // (not marked, see below)
    pub fn apply_editor_operation_fixed(
        &mut self,
        rev_editor_delta: RevisionedEditorTextDelta,
    ) -> (r: Result<(TextDelta, Vec<RevisionedEditorTextDelta>)>)
        requires
            old(self).wf(), old(self).editor_revision < usize::MAX,
        ensures
            final(self).daemon_revision == old(self).daemon_revision,
            // a rejected edit keeps the revisions, the daemon text, and the invariant
            r is Err ==> final(self).wf()
                && final(self).editor_revision == old(self).editor_revision
                && final(self).current_content@ == old(self).current_content@,
            r is Ok ==> final(self).editor_revision == old(self).editor_revision + 1,
            r is Ok ==> {
                &&& final(self).wf()
                &&& final(self).editor_queue@.len() == old(self).daemon_revision - rev_editor_delta.revision
                &&& r->Ok_0.1@.len() == final(self).editor_queue@.len()
                &&& forall|i: int| 0 <= i < r->Ok_0.1@.len() ==> r->Ok_0.1@[i].revision == final(self).editor_revision
                &&& exists|o: int| r->Ok_0.0 == op_delta(o) && final(self).current_content@ == ap(old(self).current_content@, o)
            },
    {
        let daemon_revision = rev_editor_delta.revision;

        let mut op_seq: OperationSeq;

        if !(daemon_revision <= self.daemon_revision) { return Err(Error); } // FIX: was assert!
        // "This must not happen, editor has seen a daemon revision from the future."

        let daemon_operations_to_transform = self.daemon_revision - daemon_revision;
        if !(self.editor_queue.len() >= daemon_operations_to_transform) { return Err(Error); } // FIX: was assert!
        // "Whoopsie, we don't have enough operations cached. Was this already processed?"
        let seen_operations = self.editor_queue.len() - daemon_operations_to_transform;
        let ghost q0 = ops(self.editor_queue@);
        let ghost l0 = self.last_confirmed_editor_content@;
        let confirmed_queue = drain_front(&mut self.editor_queue, seen_operations);
        assert(ops(confirmed_queue@) == q0.subrange(0, seen_operations as int));
        assert(confirmed_queue@.len() == ops(confirmed_queue@).len());
        let mut i: usize = 0;
        while i < confirmed_queue.len()
            invariant
                i <= confirmed_queue@.len(),
                seen_operations <= q0.len(),
                confirmed_queue@.len() == seen_operations,
                ops(confirmed_queue@) == q0.subrange(0, seen_operations as int),
                self.last_confirmed_editor_content@ == fold(l0, q0.subrange(0, i as int)),
            decreases confirmed_queue@.len() - i,
        {
            let confirmed_editor_op = &confirmed_queue[i];
            proof {
                assert(q0.subrange(0, i + 1) =~= q0.subrange(0, i as int).push(ops(confirmed_queue@)[i as int]));
                lemma_fold_snoc(l0, q0.subrange(0, i as int), ops(confirmed_queue@)[i as int]);
            }
            self.last_confirmed_editor_content = force_apply(
                self.last_confirmed_editor_content.as_str(),
                confirmed_editor_op.clone(),
            );
            i += 1;
        }
        proof { lemma_fold_split(l0, q0, seen_operations as int); }
        let rev_delta = match try_from_rev_ed_delta(
            rev_editor_delta,
            self.last_confirmed_editor_content.as_str(),
        ) {
            Ok(x) => x,
            Err(e) => {
                proof { assert(ops(self.editor_queue@) =~= q0.subrange(seen_operations as int, q0.len() as int)); }
                return Err(e)
            },
        };
        op_seq = op_from_delta(rev_delta.delta);
        self.editor_revision += 1; // FIX: moved here from the top

        let ghost l1 = self.last_confirmed_editor_content@;
        let ghost e = op_seq@;
        self.last_confirmed_editor_content =
            force_apply(self.last_confirmed_editor_content.as_str(), op_seq.clone());
        let (op_seq2, q2) = transform_through_operations(op_seq, &self.editor_queue);
        proof { transform_spec_inst(l1, e, ops(self.editor_queue@), op_seq2@, ops(q2@)); }
        proof {
            let u = ops(self.editor_queue@);
            assert(u =~= q0.subrange(seen_operations as int, q0.len() as int));
            assert(self.current_content@ == fold(l1, u));
        }
        op_seq = op_seq2;
        self.editor_queue = q2;
        self.operations.push(op_seq.clone());
        self.current_content = force_apply(self.current_content.as_str(), op_seq.clone());

        let deltas_for_editor = self.deltas_for_editor();
        assert(ops(self.editor_queue@).len() == self.editor_queue@.len());
        assert(self.wf());

        Ok((delta_from_op(op_seq), deltas_for_editor))
    }
    // (apply_editor_operation[_fixed] NOT marked: the fixed variant is a proposed fix not in main; main still advances editor_revision on rejected edits)

    // corr: crates/teamtype/src/ot.rs :: OTServer::deltas_for_editor
    fn deltas_for_editor(&self) -> (r: Vec<RevisionedEditorTextDelta>)
        ensures
            r@.len() == self.editor_queue@.len(),
            forall|i: int| 0 <= i < r@.len() ==> r@[i].revision == self.editor_revision,
    {
        let mut to_editor: Vec<RevisionedEditorTextDelta> = Vec::new();
        let mut document = self.last_confirmed_editor_content.clone();
        let mut i: usize = 0;
        while i < self.editor_queue.len()
            invariant
                i <= self.editor_queue@.len(),
                to_editor@.len() == i,
                forall|j: int| 0 <= j < i ==> to_editor@[j].revision == self.editor_revision,
            decreases self.editor_queue@.len() - i,
        {
            let editor_op = &self.editor_queue[i];
            let delta: TextDelta = delta_from_op(editor_op.clone());
            let ed_delta = try_from_delta_expect(delta, document.as_str());
            to_editor.push(RevisionedEditorTextDelta {
                revision: self.editor_revision,
                delta: ed_delta,
            });
            document = force_apply(document.as_str(), editor_op.clone());
            i += 1;
        }
        to_editor
    }
    // corr-end
}

// what transform_through_operations guarantees, for any start text d
pub open spec fn transform_ok(t0: int, my: Seq<int>, t: int, out: Seq<int>) -> bool {
    &&& out.len() == my.len()
    &&& forall|d: Seq<char>| #[trigger] ap(fold(d, my), t) == fold(ap(d, t0), out)
}

proof fn transform_spec_inst(d: Seq<char>, t0: int, my: Seq<int>, t: int, out: Seq<int>)
    requires transform_ok(t0, my, t, out),
    ensures ap(fold(d, my), t) == fold(ap(d, t0), out),
{}

// corr: crates/teamtype/src/ot.rs :: transform_through_operations
fn transform_through_operations(
    their_op_seq: OperationSeq,
    my_operations: &Vec<OperationSeq>,
) -> (r: (OperationSeq, Vec<OperationSeq>))
    ensures transform_ok(their_op_seq@, ops(my_operations@), r.0@, ops(r.1@)),
{
    let ghost t0 = their_op_seq@;
    let mut their_op_seq = their_op_seq;
    let mut transformed_my_operations: Vec<OperationSeq> = Vec::new();
    let mut i: usize = 0;
    while i < my_operations.len()
        invariant
            i <= my_operations@.len(),
            transformed_my_operations@.len() == i,
            forall|d: Seq<char>| #[trigger] ap(fold(d, ops(my_operations@).subrange(0, i as int)), their_op_seq@)
                == fold(ap(d, t0), ops(transformed_my_operations@)),
        decreases my_operations@.len() - i,
    {
        let mut my_op_seq = my_operations[i].clone();
        let ghost m_orig = my_op_seq@;
        let ghost t_orig = their_op_seq@;
        if my_op_seq.base_len() < their_op_seq.base_len() {
            let diff = their_op_seq.base_len() - my_op_seq.base_len();
            my_op_seq.retain(diff as u64);
            proof { assert forall|d: Seq<char>| #[trigger] ap(d, my_op_seq@) == ap(d, m_orig) by { axiom_pad(d, m_orig, diff as nat); } }
        } else {
            let diff = my_op_seq.base_len() - their_op_seq.base_len();
            their_op_seq.retain(diff as u64);
            proof { assert forall|d: Seq<char>| #[trigger] ap(d, their_op_seq@) == ap(d, t_orig) by { axiom_pad(d, t_orig, diff as nat); } }
        }
        let ghost m = my_op_seq@;
        let ghost t = their_op_seq@;
        assert(forall|d: Seq<char>| #[trigger] ap(d, m) == ap(d, m_orig));
        assert(forall|d: Seq<char>| #[trigger] ap(d, t) == ap(d, t_orig));
        let (my_prime, their_prime) = my_op_seq.transform_or_panic(&their_op_seq);
        let ghost prev = ops(transformed_my_operations@);
        transformed_my_operations.push(my_prime);
        their_op_seq = their_prime;
        proof {
            let my_s = ops(my_operations@);
            assert(my_s.subrange(0, i + 1) =~= my_s.subrange(0, i as int).push(m_orig));
            assert(ops(transformed_my_operations@) =~= prev.push(my_prime@));
            assert forall|d: Seq<char>| #[trigger] ap(fold(d, my_s.subrange(0, i + 1)), their_op_seq@)
                == fold(ap(d, t0), ops(transformed_my_operations@)) by {
                let x = fold(d, my_s.subrange(0, i as int));
                lemma_fold_snoc(d, my_s.subrange(0, i as int), m_orig);
                lemma_fold_snoc(ap(d, t0), prev, my_prime@);
                axiom_tp1(x, m, t);
                assert(ap(x, m) == ap(x, m_orig));
                assert(ap(x, t) == ap(x, t_orig));
                assert(ap(x, t_orig) == fold(ap(d, t0), prev));
            }
        }
        i += 1;
    }
    proof { assert(ops(my_operations@).subrange(0, i as int) =~= ops(my_operations@)); }
    (their_op_seq, transformed_my_operations)
}
// corr-end

fn main() {}

} // verus!
