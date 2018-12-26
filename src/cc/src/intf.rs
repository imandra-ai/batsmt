
use {
    batsmt_core::{backtrack, },
    batsmt_theory::Ctx,
    crate::{types::*},
};

/// Interface satisfied by implementations of the congruence closure.
pub trait CC<C: Ctx> : backtrack::Backtrackable {
    /// `cc.merge(t1,t2,lit)` merges `t1` and `t2` with explanation `lit`.
    fn merge(&mut self, m: &C::M, t1: C::AST, t2: C::AST, lit: C::B);

    /// `cc.distinct(terms,lit)` asserts that all elements of `terms` are disjoint
    fn distinct(&mut self, m: &C::M, ts: &[C::AST], lit: C::B);

    /// Add a binding term<=>literal to the congruence closure.
    ///
    /// This is typically called before solving, so as to add terms once
    /// and for all, and so that the congruence closure can propagate
    /// literals back to the SAT solver.
    fn add_literal(&mut self, _m: &C::M, _t: C::AST, _lit: C::B) {}

    /// Check if the set of `merge` and `distinct` seen so far is consistent.
    ///
    /// Returns `Ok(props)` if the result is safisfiable with propagations `props`,
    /// and `Err(c)` if `c` is a valid conflict clause that contradicts
    /// the current trail.
    fn final_check(&mut self, m: &C::M) -> Result<&PropagationSet<C::B>, Conflict<C::B>>;

    /// Same as `final_check`, but never called if `has_partial_check() == false`.
    fn partial_check(&mut self, m: &C::M) -> Result<&PropagationSet<C::B>, Conflict<C::B>> {
        unimplemented!("partial check")  // FIXME: instead, return empty propagations
    }

    /// Can it handle partial checks?
    fn has_partial_check() -> bool { false }

    /// Description of this particular implementation
    fn impl_descr() -> &'static str;

    /// Explain given propagation.
    fn explain_propagation(&mut self, m: &C::M, p: C::B) -> &[C::B];
}
