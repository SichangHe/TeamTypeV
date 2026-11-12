// (authored by agents) Verus proof that an edit script accepted by `types::chunks_reconstruct`
// (what `types::checked_diff` returns) turns the old text into the new one, in the operational-transform
// semantics `sem` of the source-derived operational-transform 0.6.1 copy (tp1_id.rs).
use vstd::prelude::*;
mod tp1_id;
use tp1_id::*;

verus! {

// dissimilar::Chunk with its text as characters
pub enum Ck { Equal(Seq<char>), Delete(Seq<char>), Insert(Seq<char>) }

// `impl From<Vec<Chunk>> for TextDelta`: Equal -> retain(n), Delete -> delete(n), Insert -> insert(s)
pub open spec fn ck_op(c: Ck) -> SOp {
    match c { Ck::Equal(s) => SOp::R(s.len()), Ck::Delete(s) => SOp::D(s.len()), Ck::Insert(s) => SOp::I(s) }
}
pub open spec fn script_ops(cs: Seq<Ck>) -> Seq<SOp>
    decreases cs.len(),
{
    if cs.len() == 0 { Seq::empty() } else { seq![ck_op(cs[0])].add(script_ops(cs.drop_first())) }
}

// `types::chunks_reconstruct(chunks, a, b)`: strip_prefix of each chunk from the remaining old / new text
pub open spec fn reconstructs(cs: Seq<Ck>, a: Seq<char>, b: Seq<char>) -> bool
    decreases cs.len(),
{
    if cs.len() == 0 { a.len() == 0 && b.len() == 0 } else {
        match cs[0] {
            Ck::Equal(s) => a.len() >= s.len() && b.len() >= s.len()
                && a.take(s.len() as int) == s && b.take(s.len() as int) == s
                && reconstructs(cs.drop_first(), a.skip(s.len() as int), b.skip(s.len() as int)),
            Ck::Delete(s) => a.len() >= s.len() && a.take(s.len() as int) == s
                && reconstructs(cs.drop_first(), a.skip(s.len() as int), b),
            Ck::Insert(s) => b.len() >= s.len() && b.take(s.len() as int) == s
                && reconstructs(cs.drop_first(), a, b.skip(s.len() as int)),
        }
    }
}

// The script reads exactly the old text and, applied to it, yields exactly the new text.
pub proof fn theorem_script_correct(cs: Seq<Ck>, a: Seq<char>, b: Seq<char>)
    requires reconstructs(cs, a, b),
    ensures cons(script_ops(cs)) == a.len(), sem(a, script_ops(cs)) == b,
    decreases cs.len(),
{
    if cs.len() == 0 {
        assert(script_ops(cs) =~= Seq::<SOp>::empty());
        assert(a =~= Seq::<char>::empty());
        assert(b =~= Seq::<char>::empty());
    } else {
        let o = ck_op(cs[0]);
        let rest = cs.drop_first();
        let (a2, b2) = match cs[0] {
            Ck::Equal(s) => (a.skip(s.len() as int), b.skip(s.len() as int)),
            Ck::Delete(s) => (a.skip(s.len() as int), b),
            Ck::Insert(s) => (a, b.skip(s.len() as int)),
        };
        theorem_script_correct(rest, a2, b2);
        let q = script_ops(rest);
        let c0 = cons_of(o);
        assert(script_ops(cs) =~= seq![o].add(q));
        // the first op reads c0 characters, the rest reads |a2|
        match cs[0] {
            Ck::Equal(s) => { assert(c0 == s.len()); }
            Ck::Delete(s) => { assert(c0 == s.len()); }
            Ck::Insert(s) => { assert(c0 == 0); }
        }
        assert(a.len() == c0 + a2.len());
        lemma_one(a.take(c0 as int), o);
        lemma_split(a, seq![o], q);
        assert(cons(seq![o]) == c0);
        let head = sem(a.take(c0 as int), seq![o]);
        let tailt = sem(a.skip(c0 as int), q);
        assert(a.skip(c0 as int) =~= a2);
        match cs[0] {
            Ck::Equal(s) => {
                assert(head == s);
                assert(a.take(s.len() as int) == s);
                assert(b =~= s + b2);
            }
            Ck::Delete(s) => {
                assert(head =~= Seq::<char>::empty());
                assert(b =~= Seq::<char>::empty() + b2);
            }
            Ck::Insert(s) => {
                assert(head == s);
                assert(a.take(0) =~= Seq::<char>::empty());
                assert(b =~= s + b2);
            }
        }
    }
}

// Equal texts: `checked_diff` returns [Equal(a)] (or nothing for the empty text): an all-Retain op
pub proof fn lemma_equal_texts_all_retain(a: Seq<char>)
    ensures
        forall|i: int| 0 <= i < script_ops(seq![Ck::Equal(a)]).len() ==> script_ops(seq![Ck::Equal(a)])[i] is R,
        cons(script_ops(seq![Ck::Equal(a)])) == a.len(),
{
    let cs = seq![Ck::Equal(a)];
    assert(cs.drop_first() =~= Seq::<Ck>::empty());
    assert(script_ops(Seq::<Ck>::empty()) =~= Seq::<SOp>::empty());
    assert(cs[0] == Ck::Equal(a));
    assert(script_ops(cs) =~= seq![SOp::R(a.len())].add(Seq::<SOp>::empty()));
    assert(seq![SOp::R(a.len())].add(Seq::<SOp>::empty()) =~= seq![SOp::R(a.len())]);
    lemma_one(a, SOp::R(a.len()));
}

} // verus!
fn main() {}
