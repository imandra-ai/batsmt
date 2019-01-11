
use {
    std::{hash::Hash, fmt, },
    batsmt_theory::{self as theory, Actions},
    batsmt_core::{backtrack, },
};

/// A view of terms adapted for the congruence closure.
#[derive(Debug,Clone)]
pub enum CCView<'a,Fun,AST> {
    Bool(bool),
    Apply(&'a Fun, &'a [AST]),
    ApplyHO(&'a AST, &'a [AST]),
    Eq(&'a AST, &'a AST),
    Distinct(&'a [AST]),
    Opaque(&'a AST), // a foreign term
}

/// The context needed by the congruence closure.
///
/// It provides a notion of boolean literals, functions, terms, as well as
/// a way to deconstruct terms in the most convenient way.
pub trait Ctx : theory::Ctx {
    type Fun : Eq + Hash + Clone;

    /// View a term as an equality or function application.
    fn view_as_cc_term(&self, t: &Self::AST) -> CCView<Self::Fun, Self::AST>;

    /// Obtain true/false terms.
    fn get_bool_term(&self, b: bool) -> Self::AST;
}

/// Interface satisfied by implementations of the congruence closure.
pub trait CC<C: Ctx> : backtrack::Backtrackable<C> {
    /// `cc.merge(t1,t2,lit)` merges `t1` and `t2` with explanation `lit`.
    fn merge(&mut self, m: &C, t1: C::AST, t2: C::AST, lit: C::B);

    /// `cc.distinct(terms,lit)` asserts that all elements of `terms` are disjoint
    fn distinct(&mut self, m: &C, ts: &[C::AST], lit: C::B);

    /// Add a binding term<=>literal to the congruence closure.
    ///
    /// This is typically called before solving, so as to add terms once
    /// and for all, and so that the congruence closure can propagate
    /// literals back to the SAT solver.
    fn add_literal(&mut self, _m: &C, _t: C::AST, _lit: C::B) {}

    /// Check if the set of `merge` and `distinct` seen so far is consistent.
    ///
    /// Returns `Ok(props)` if the result is safisfiable with propagations `props`,
    /// and `Err(c)` if `c` is a valid conflict clause that contradicts
    /// the current trail.
    fn final_check<A>(&mut self, m: &C, a: &mut A) where A: Actions<C>;

    /// Same as `final_check`, but never called if `has_partial_check() == false`.
    fn partial_check<A>(&mut self, _m: &C, _a: &mut A) where A: Actions<C> {}

    /// Can it handle partial checks?
    fn has_partial_check() -> bool { false }

    /// Description of this particular implementation
    fn impl_descr() -> &'static str;

    /// Explain why `p` was propagated
    fn explain_prop(&mut self, m: &C, p: C::B) -> &[C::B];
}
