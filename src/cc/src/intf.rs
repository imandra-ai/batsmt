
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
    fn merge(&mut self, m: &mut C, t1: C::AST, t2: C::AST, lit: C::B);

    /// `cc.distinct(terms,lit)` asserts that all elements of `terms` are disjoint
    fn distinct(&mut self, m: &mut C, ts: &[C::AST], lit: C::B);

    /// Add a binding term<=>literal to the congruence closure.
    ///
    /// This is typically called before solving, so as to add terms once
    /// and for all, and so that the congruence closure can propagate
    /// literals back to the SAT solver.
    fn add_literal(&mut self, _m: &mut C, _t: C::AST, _lit: C::B) {}

    /// Check if the set of `merge` and `distinct` seen so far is consistent.
    ///
    /// Returns `Ok(props)` if the result is safisfiable with propagations `props`,
    /// and `Err(c)` if `c` is a valid conflict clause that contradicts
    /// the current trail.
    fn final_check<A>(&mut self, m: &mut C, a: &mut A) where A: Actions<C>;

    /// Same as `final_check`, but never called if `has_partial_check() == false`.
    fn partial_check<A>(&mut self, _m: &mut C, _a: &mut A) where A: Actions<C> {}

    /// Can it handle partial checks?
    fn has_partial_check() -> bool { false }

    /// Description of this particular implementation
    fn impl_descr() -> &'static str;

    /// Enable/disable boolean propagation.
    fn enable_propagation(&mut self, _on: bool) {}

    /// Explain why `p` was propagated
    fn explain_prop(&mut self, m: &C, p: C::B) -> &[C::B];
}

/// A term adapted for if-then-else.
#[derive(Debug,Clone)]
pub enum IteView<'a, AST>{
    Ite(&'a AST, &'a AST, &'a AST),
    Other(&'a AST),
}

pub trait HasIte<AST> {
    /// View a term as a if-then-else.
    fn view_as_ite<'a>(&'a self, t: &'a AST) -> IteView<'a, AST>;
}

/// A term adapted for injective functions.
#[derive(Debug,Clone)]
pub enum InjectiveView<'a, F, AST>{
    AppInjective(&'a F, &'a [AST]),
    Other(&'a AST),
}

pub trait HasInjectivity<AST> {
    type F : Eq + Hash + Clone + fmt::Debug;

    /// View the term as an injective function, if it is.
    ///
    /// This means that if `f(t1…tn) = f(u1…un)` then `t1=u1 ∧ … ∧ tn=un`
    fn view_as_injective<'a>(&'a self, t: &'a AST) -> InjectiveView<'a, Self::F, AST>;
}

pub trait HasDisjointness<AST> {
    type F : Eq + Clone + fmt::Debug;

    /// Does the given term have a label?
    ///
    /// This means any term with a distinct label is disequal to this term.
    fn get_disjoint_label(&self, t: &AST) -> Option<Self::F>;
}

/// A view of terms with selector functions over injective functions.
///
/// A selector `select-f-idx` is a term
/// satisfying `select-f-idx(f(t1…tn)) = t_idx`.
pub enum SelectorView<'a, F, AST> {
    Select {
        f: &'a F,
        idx: u32,
        sub: &'a AST, // in what term?
    },
    Other(&'a AST),
}

pub trait HasSelector<AST> : HasInjectivity<AST> {
    /// View a term as a selector.
    fn view_as_selector<'a>(&'a self, t: &'a AST) -> SelectorView<'a, Self::F, AST>;
}

pub enum ConstructorView<'a, F, AST> {
    AppConstructor(&'a F, &'a [AST]),
    Select {
        f: &'a F,
        idx: u32,
        sub: &'a AST, // in what term?
    },
    Other(&'a AST),
}

/// Injectivity but for constructors (also implying disjointness).
pub trait HasConstructor<AST> {
    type F : Eq + Hash + Clone + fmt::Debug;

    /// View the term as an constructor application, if it is.
    ///
    /// This means that if `f(t1…tn) = f(u1…un)` then `t1=u1 ∧ … ∧ tn=un`,
    /// and that `f(…) != g(…)` for any distinct constructors `f` and `g`.
    fn view_as_constructor<'a>(&'a self, t: &'a AST) -> ConstructorView<'a, Self::F, AST>;
}
