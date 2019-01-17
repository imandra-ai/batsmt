
use {
    std::{hash::Hash, fmt, },
    batsmt_theory::{self as theory, Actions},
    batsmt_core::{backtrack, },
    batsmt_pretty as pp,
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

impl<'a,Fun,AST> CCView<'a,Fun,AST> {
    /// Iterate on immediate subterms that are relevant to congruence.
    pub fn iter_subterms<F>(&self, mut f: F) where F: FnMut(&'a AST) {
        match self {
            CCView::Bool(_) | CCView::Opaque(..) => (),
            CCView::Eq(a,b) => {
                f(a);
                f(b);
            },
            CCView::Apply(_, args) | CCView::Distinct(args) => {
                for u in args.iter() { f(u) }
            },
            CCView::ApplyHO(f0, args) => {
                f(f0);
                for u in args.iter() { f(u) }
            },
        }
    }

    /// Needs a signature in the congruence closure?
    pub(crate) fn needs_sig(&self) -> bool {
        match self {
            CCView::Opaque(..) | CCView::Bool(..) => false,
            CCView::Eq(..) | CCView::Apply(_, ..) | CCView::Distinct(..) | CCView::ApplyHO(..) => true,
        }
    }
}

/// The context needed by the congruence closure.
///
/// It provides a notion of boolean literals, functions, terms, as well as
/// a way to deconstruct terms in the most convenient way.
pub trait Ctx : theory::Ctx {
    type Fun : Eq + Hash + Clone + fmt::Debug;

    /// View a term as an equality or function application.
    fn view_as_cc_term<'a>(&'a self, t: &'a Self::AST) -> CCView<'a, Self::Fun, Self::AST>;

    /// Obtain true/false terms.
    fn get_bool_term(&self, b: bool) -> Self::AST;
}

/// An empty type, convenient when there is no notion of `Fun` in terms.
#[derive(Eq,PartialEq,Clone,Debug,Hash)]
pub enum Void{} // empty type

/// Print a term.
pub(crate) fn pp_t<'a,C:Ctx>(
    c: &'a C, t: &'a C::AST
) -> impl 'a + fmt::Display + fmt::Debug + pp::Pretty {
    theory::pp_ast(c,t)
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
