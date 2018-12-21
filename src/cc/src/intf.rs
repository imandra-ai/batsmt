
use {
    batsmt_core::{AST, backtrack, },
    crate::{types::*},
};

/// A local, temporary object one can add assumptions to before calling `check`.
pub trait Check<B:BoolLit> {
    /// `cc.merge(t1,t2,lit)` merges `t1` and `t2` with explanation `lit`.
    fn merge(&mut self, t1: AST, t2: AST, lit: B);

    /// `cc.distinct(terms,lit)` asserts that all elements of `terms` are disjoint
    fn distinct(&mut self, ts: &[AST], lit: B);

    /// Add a binding term<=>literal to the congruence closure.
    ///
    /// This is typically called before solving, so as to add terms once
    /// and for all, and so that the congruence closure can propagate
    /// literals back to the SAT solver.
    fn add_literal(&mut self, _t: AST, _lit: B) {}

    /// Check if the set of `merge` and `distinct` seen so far is consistent.
    ///
    /// Returns `Ok(props)` if the result is safisfiable with propagations `props`,
    /// and `Err(c)` if `c` is a valid conflict clause that contradicts
    /// the current trail.
    fn final_check(&mut self) -> Result<&PropagationSet<B>, Conflict<B>>;

    /// Same as `final_check`, but never called if `has_partial_check() == false`.
    fn partial_check(&mut self) -> Result<&PropagationSet<B>, Conflict<B>> {
        unimplemented!("partial check")  // FIXME: instead, return empty propagations
    }
}

/// Interface satisfied by implementations of the congruence closure.
pub trait CC<B:BoolLit> : backtrack::Backtrackable {
    /// Local type used to add assumptions and solve.
    type Checker : Check<B>;

    /// Obtain a local solver instance.
    ///
    /// This solver instance can be used to append some (dis)equalities
    /// to the conjunction, before it is consumed by calling `final_check`
    /// or `partial_check`.
    fn checker(&mut self) -> &mut Self::Checker;

    /// Can it handle partial checks?
    fn has_partial_check() -> bool { false }

    /// Description of this particular implementation
    fn impl_descr(&self) -> &'static str;
}
