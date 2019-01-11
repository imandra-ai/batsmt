
//! General notion of Theory.
//!
//! A theory can decide conjunctions of atoms that belong to some fragment of terms.
//! It is backtrackable (following the SAT solver).
//!
//! Such a theory should be usable to implement a CDCL(T) solver (see `batsmt-solver`),
//! on its own for contextual simplification, or with some other boolean
//! enumerator such as a BDD.
//! For this reason, it abstracts over the type of boolean literals (`BoolLit`).

use {
    std::{ops::{Deref,Not}, hash::Hash, fmt},
    batsmt_core::{ backtrack::Backtrackable, gc, },
    batsmt_pretty as pp,
};

pub mod lit_map;

// re-exports for litmap
pub use {
    crate::lit_map::{LitMap, Builtins as LitMapBuiltins, },
};

/// Abstract notion of boolean literals.
///
/// A literal must be copyable, printable, comparable, hashable,
/// and have a notion of negation.
///
/// It must be the case that `!!b` is the same as `b`.
pub trait BoolLit : fmt::Debug + Eq + Ord + Hash + Copy + Not<Output=Self> {
    fn abs(&self) -> Self;

    /// Identity or negation depending on `sign` being true or false.
    #[inline(always)]
    fn apply_sign(&self, sign: bool) -> Self {
        if sign { *self } else { ! *self }
    }
}

/// Context that has a notion of boolean literals.
pub trait BoolLitCtx {
    type B : BoolLit;
}

/// Context that has a notion of boolean literal, as well as a notion of term.
pub trait Ctx : BoolLitCtx {
    type AST : Eq + Hash + Clone + fmt::Debug;

    /// Pretty print a term.
    fn pp_ast(&self, t: &Self::AST, ctx: &mut pp::Ctx);
}

/// A theory-level literal, either a boolean literal, or a boolean term plus a sign.
///
/// The conversion to SAT literals of the latter
/// is done automatically and theories
/// should not have to worry about it.
#[derive(Eq,PartialEq)]
pub enum TheoryLit<C:Ctx> {
    T(C::AST, bool), // theory lit
    BLazy(C::AST, bool), // to be turned into B
    B(C::B),
}

/// A temporary theory-level clause, such as a lemma or theory conflict.
///
/// It is composed of a set of `TheoryLit`.
#[derive(Clone,Copy)]
pub struct TheoryClauseRef<'a,C:Ctx> {
    lits: &'a [TheoryLit<C>],
}

/// A set of theory clauses, with efficient append.
#[derive(Clone)]
pub struct TheoryClauseSet<C:Ctx> {
    lits: Vec<TheoryLit<C>>, // clause lits
    offsets: Vec<(usize,usize)>, // slices in `lits`
}

/// A set of actions available to theories.
///
/// A theory can use these actions to signal its caller that some
/// literals can be propagated, or that the current set of literals
/// is T-inconsistent.
pub trait Actions<C:Ctx> {
    /// Add a lemma-on-demand.
    ///
    /// NOTE: this is not well supported yet.
    fn add_lemma(&mut self, c: &[C::B]);

    /// Propagate the given boolean literal.
    ///
    /// The boolean solver is allowed to ask for an explanation
    /// using `explain_propagation` later.
    fn propagate(&mut self, p: C::B);

    /// Add a conflit clause.
    ///
    /// This clause should be a valid theory lemma (a valid tautology) that
    /// is false in the current model.
    ///
    /// ## Params
    /// - `costly`, if true, ask that the boolean solver keeps this conflict
    ///     instead of throwing it away immediately after conflict analysis.
    ///     The solver might still garbage collect it later.
    fn raise_conflict(&mut self, c: &[C::B], costly: bool);

    /// Map a theory literal into a proper boolean literal.
    fn map_lit(&mut self, m: &C, lit: TheoryLit<C>) -> C::B;

    /// Check if a conflict was found yet.
    ///
    /// This is useful to interrupt work early.
    fn has_conflict(&self) -> bool;
}

/// The theory subset of the (partial) model picked by the SAT solver.
///
/// This is given to the theory in order to check its validity. It doesn't show
/// purely boolean literals.
pub struct Trail<'a,C:Ctx>(pub(crate) &'a [(C::AST,bool,C::B)]);

/// Interface satisfied by a SMT theory.
///
/// A theory is responsible for enforcing the semantics of some
/// of the boolean literals.
pub trait Theory<C:Ctx> : Backtrackable<C>{
    /// Check a full model.
    ///
    /// ## Params:
    ///
    /// - `trail` contains triples `(term, bool, literal)` where `literal`
    ///     is `term <=> bool` and the current model contains `literal`
    /// - `acts` is a set of actions available to the theory.
    fn final_check<A:Actions<C>>(&mut self, _ctx: &mut C, acts: &mut A, trail: &Trail<C>);

    /// Check a partial model.
    ///
    /// This is only called if `self.has_partial_check()` is `true`.
    ///
    /// The parameters are similar to those of `final_check`, but
    /// this function is allowed to not fully check the model, and `trail`
    /// only contains _new_ literals (since the last call to `partial_check`).
    /// It will be called more often than `final_check` so it should be efficient.
    fn partial_check<A:Actions<C>>(&mut self, _ctx: &mut C, _acts: &mut A, _trail: &Trail<C>) {}

    /// Does the theory handle partial checks?
    ///
    /// If `false`, the method `partial_check` will never be called,
    /// and `final_check` will get the whole trail;
    /// If `true`, the method `partial_check` will be called often,
    /// and `final_check` will have an empty trail.
    fn has_partial_check() -> bool { false }

    /// Add a binding term<=>literal to the theory.
    ///
    /// This is typically called before solving, so as to add terms once
    /// and for all, and so that the theory can propagate
    /// literals back to the SAT solver.
    fn add_literal(&mut self, _ctx: &C, _t: C::AST, _lit: C::B) {}

    /// Ask the theory to explain why it propagated literal `lit`.
    ///
    /// The result must be a set `g` of literals which are true in the current
    /// trail, and such that `g => p` is a T-tautology.
    ///
    /// ## Params
    ///
    /// - `ctx`: the theory context.
    /// - `(t,sign)`: the signed theory atom corresponding to `p`.
    /// - `p`: the raw boolean literal whose propagation must be explained.
    fn explain_propagation(&mut self, ctx: &C, t: C::AST, sign: bool, p: C::B) -> &[C::B];
}

/// Statistics.
#[derive(Clone,Debug)]
pub struct Stats {
    pub conflicts: u64,
    pub propagations: u64,
    pub lemmas: u64,
}

mod stats {
    use {std::fmt, super::*};
    impl Stats {
        /// New statistics accumulator.
        pub fn new() -> Self {
            Stats{ conflicts: 0, propagations: 0, lemmas: 0, }
        }
    }
    impl fmt::Display for Stats {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "theory.conflicts {}, theory.propagations {}, theory.lemmas {}",
                   self.conflicts, self.propagations, self.lemmas)
        }
    }
    impl Default for Stats {
        fn default() -> Self { Stats::new() }
    }
}

mod theory_lit {
    use super::*;

    impl<C:Ctx> Clone for TheoryLit<C> {
        fn clone(&self) -> Self {
            match self {
                TheoryLit::B(a) => TheoryLit::B(*a),
                TheoryLit::T(t,sign) => TheoryLit::T(t.clone(), *sign),
                TheoryLit::BLazy(t,sign) => TheoryLit::BLazy(t.clone(), *sign),
            }
        }
    }

    impl<C:Ctx> Copy for TheoryLit<C> where C::B: Copy, C::AST: Copy {}

    impl<C:Ctx> TheoryLit<C> {
        /// Make a theory literal.
        ///
        /// This literal will map bidirectionally with the term, and
        /// will be passed to the Theory whenever it's decided by the SAT solver.
        pub fn new_t(ast: C::AST, sign: bool) -> Self { TheoryLit::T(ast,sign) }

        /// Make a lazy pure boolean literal.
        ///
        /// This designates a pure boolean literal that will live in the SAT
        /// solver but will not be passed to the theory.
        /// The same term will always map to the same boolean literal.
        pub fn new_b(ast: C::AST, sign: bool) -> Self { TheoryLit::BLazy(ast,sign) }

        /// Wrap a pure boolean literal.
        ///
        /// This pure SAT literal will never be passed to the theory.
        /// It is given to the SAT solver as is.
        pub fn from_blit(b: C::B) -> Self { TheoryLit::B(b) }

        /// Is is a theory literal (i.e. given to the theory when in a partial model)?
        pub fn is_theory(&self) -> bool { match self { TheoryLit::T(..) => true, _ => false } }

        /// Is it a pure boolean literal (i.e. not a theory literal)?
        pub fn is_pure_bool(&self) -> bool {
            match self { TheoryLit::BLazy(..) | TheoryLit::B(..) => true, _ => false }
        }
    }

    impl<C:Ctx> fmt::Debug for TheoryLit<C>
        where C::AST: fmt::Debug,
              C::B: fmt::Debug
    {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            match self {
                TheoryLit::B(lit) => write!(fmt, "{:?}", lit),
                TheoryLit::T(t,sign) => {
                    let s = if *sign { "t+" } else { "t-" };
                    write!(fmt, "{} {:?}", s, t)
                },
                TheoryLit::BLazy(t,sign) => {
                    let s = if *sign { "b+" } else { "b-" };
                    write!(fmt, "{} {:?}", s, t)
                },
            }
        }
    }

    impl<C:Ctx> pp::Pretty1<C> for TheoryLit<C> {
        fn pp1_into(&self, c: &C, ctx: &mut pp::Ctx) {
            match self {
                TheoryLit::B(lit) => {
                    pp::Pretty::pp_into(&pp::dbg(lit), ctx);
                },
                TheoryLit::T(t,sign) => {
                    let s = if *sign { "t+" } else { "t-" };
                    ctx.sexp(|ctx| {
                        ctx.str(s).space();
                        c.pp_ast(t, ctx);
                    });
                },
                TheoryLit::BLazy(t,sign) => {
                    let s = if *sign { "b+" } else { "b-" };
                    ctx.sexp(|ctx| {
                        ctx.str(s).space();
                        c.pp_ast(t, ctx); });
                },
            }
        }
    }

    impl<C:Ctx> From<(C::AST,bool)> for TheoryLit<C> {
        fn from(p: (C::AST,bool)) -> Self { Self::new_t(p.0,p.1) }
    }

    // easy negation
    impl<C:Ctx> Not for TheoryLit<C> {
        type Output = Self;
        /// Negation on the AST-based literals
        fn not(self) -> Self {
            match self {
                TheoryLit::B(lit) => TheoryLit::B(!lit),
                TheoryLit::T(t,sign) => Self::new_t(t, !sign),
                TheoryLit::BLazy(t,sign) => Self::new_b(t, !sign),
            }
        }
    }
}

mod theory_clause {
    use super::*;

    impl<'a,C:Ctx> TheoryClauseRef<'a,C> {
        pub fn iter(&'a self) -> impl Iterator<Item=TheoryLit<C>> + 'a {
            self.lits.iter().cloned()
        }
    }

    impl<'a,C:Ctx> fmt::Debug for TheoryClauseRef<'a,C> {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "[")?;
            for lit in self.iter() { lit.fmt(fmt)? }
            write!(fmt, "]")
        }
    }

    impl<'a,C:Ctx> Deref for TheoryClauseRef<'a,C> {
        type Target = [TheoryLit<C>];
        fn deref(&self) -> &Self::Target { &self.lits }
    }

    // Print a list of literals
    impl<'a,C:Ctx> pp::Pretty1<C> for TheoryClauseRef<'a,C> {
        fn pp1_into(&self, c: &C, ctx: &mut pp::Ctx) {
            ctx.sexp(|ctx| {
                ctx.iter(pp::pair(" ∨", pp::space()),
                    self.lits.iter().map(|lit| lit.pp(c)));
            });
        }
    }
}

impl<C:Ctx> TheoryClauseSet<C> {
    /// New set of clauses.
    pub fn new() -> Self {
        Self {lits: Vec::new(), offsets: Vec::new() }
    }

    /// Remove all clauses internally.
    ///
    /// Internal storage is kept.
    pub fn clear(&mut self) {
        self.offsets.clear();
        self.lits.clear();
    }

    /// Push a clause into the set.
    pub fn push<L>(&mut self, c: &[L])
        where L: Clone + Into<TheoryLit<C>>
    {
        let idx = self.lits.len();
        self.offsets.push((idx, c.len()));
        self.lits.extend(c.iter().map(|x| x.clone().into()));
    }

    /// Push a clause (as an iterator) into the set.
    pub fn push_iter<U, I>(&mut self, i: I)
        where I: Iterator<Item=U>, U: Into<TheoryLit<C>>
    {
        let idx = self.lits.len();
        self.lits.extend(i.map(|x| x.into()));
        let len = self.lits.len() - idx;
        self.offsets.push((idx, len));
    }

    /// Iterate over the contained clauses.
    ///
    /// Use `c.into()` over the slices to turn them into proper `TheoryClause`,
    /// if needed.
    pub fn iter<'a>(&'a self) -> impl Iterator<Item=TheoryClauseRef<'a,C>> {
        CSIter{cs: &self, idx: 0}
    }
}

// iterator over clauses
struct CSIter<'a, C:Ctx> {
    cs: &'a TheoryClauseSet<C>,
    idx: usize, // in `cs.offsets`
}

mod theory_clause_set {
    use super::*;

    impl<C:Ctx> fmt::Debug for TheoryClauseSet<C> {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "clause_set(")?;
            for c in self.iter() {
                fmt::Debug::fmt(&c, fmt)?
            }
            write!(fmt, ")")
        }
    }

    // the iterator over clauses
    impl<'a, C:Ctx> Iterator for CSIter<'a, C> {
        type Item = TheoryClauseRef<'a, C>;

        fn next(&mut self) -> Option<Self::Item> {
            let cs = self.cs;
            if self.idx >= cs.offsets.len() {
                None
            } else {
                let (off,len) = cs.offsets[self.idx];
                self.idx += 1;
                Some(TheoryClauseRef{lits: &cs.lits[off..off+len]})
            }
        }
    }

    impl<C:Ctx> gc::HasInternalMemory for TheoryClauseSet<C> {
        fn reclaim_unused_memory(&mut self) {
            self.lits.shrink_to_fit();
            self.offsets.shrink_to_fit();
        }
    }
}

impl<'a, C:Ctx> Trail<'a, C> {
    #[inline(always)]
    /// Access the underlying items.
    pub fn as_slice(&self) -> &'a [(C::AST,bool,C::B)] { &self.0 }

    #[inline(always)]
    /// Build a trail from this slice.
    pub fn from_slice(a: &'a [(C::AST,bool,C::B)]) -> Self { Trail(a) }

    #[inline(always)]
    /// Empty trail.
    pub fn empty() -> Self { Trail(&[]) }

    /// Iterate on the underlying items.
    pub fn iter(&self) -> impl Iterator<Item=(C::AST,bool,C::B)> + 'a {
        self.0.iter().cloned()
    }

    /// Number of literals assigned.
    #[inline(always)]
    pub fn len(&self) -> usize { self.0.len() }
}

/// Create a temporary printing object from `m` to display the given term.
pub fn pp_ast<'a, C:Ctx>(m: &'a C, t: &C::AST) -> impl 'a + fmt::Debug + fmt::Display + pp::Pretty {
    pp0::PP(m,t.clone())
}

mod pp0 {
    use super::*;
    pub(super) struct PP<'a, C:Ctx>(pub &'a C, pub C::AST);

    impl<'a, C:Ctx> pp::Pretty for PP<'a,C> {
        fn pp_into(&self, ctx: &mut pp::Ctx) {
            self.0.pp_ast(&self.1, ctx)
        }
    }
    impl<'a, C:Ctx> fmt::Debug for PP<'a, C> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result
        { pp::Pretty::pp_fmt(&self,out,true) }
    }
    impl<'a, C:Ctx> fmt::Display for PP<'a, C> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result
        { pp::Pretty::pp_fmt(&self,out,false) }
    }
}


/// A basic implementation of boolean literals using signed integers
pub mod int_lit {
    /// A very simple representation of literals using signed integers.
    ///
    /// It doesn't correspond to any solver, but can be useful for testing.
    #[derive(Copy,Clone,Eq,PartialEq,Ord,PartialOrd,Hash,Debug)]
    pub struct Lit(i32);

    impl std::ops::Not for Lit {
        type Output = Lit;
        fn not(self) -> Self { debug_assert_ne!(self.0, 0); Lit(-self.0) }
    }

    impl super::BoolLit for Lit {
        #[inline(always)]
        fn abs(&self) -> Self { Lit(self.0.abs()) }
    }
}

pub type IntLit = int_lit::Lit;

/// Basic actions, mostly useful for testing.
pub struct SimpleActions<C:Ctx> {
    confl: Option<Vec<C::B>>,
    costly: bool,
    props: Vec<C::B>,
    lemmas: Vec<Vec<C::B>>,
    #[allow(unused)]
    mk_lit: Box<Fn() -> C::B>, // FIXME: actual litmap or something?
}

impl<C:Ctx> Actions<C> for SimpleActions<C> {
    fn has_conflict(&self) -> bool { self.confl.is_some() }

    fn propagate(&mut self, p: C::B) {
        if !self.has_conflict() {
            self.props.push(p)
        }
    }
    fn add_lemma(&mut self, c: &[C::B]) {
        if !self.has_conflict() {
            self.lemmas.push(c.iter().cloned().collect())
        }
    }
    fn raise_conflict(&mut self, c: &[C::B], costly: bool) {
        if !self.has_conflict() {
            self.clear();
            self.costly = costly;
            self.confl = Some(c.iter().cloned().collect());
        }
    }
    fn map_lit(&mut self, _m: &C, _lit: TheoryLit<C>) -> C::B {
        unimplemented!("map-lit")
    }
}

impl<C:Ctx> SimpleActions<C> {
    /// New set of actions.
    pub fn new<F>(f: F) -> Self
        where F: 'static + Fn() -> C::B
    {
        let mk_lit = Box::new(f);
        SimpleActions {
            mk_lit, lemmas: vec!(), props: vec!(),
            confl: None, costly: false
        }
    }

    /// Reset internal state.
    pub fn clear(&mut self) {
        self.confl = None;
        self.props.clear();
        self.lemmas.clear();
    }

    /// Get results.
    ///
    /// Returns `Ok((props, lemmas))` if the theory deemed the trail satisfiable,
    /// `Err(conflict)` if `conflict` is a theory lemma that is currently false.
    pub fn get(&self) -> Result<(&[C::B], &[Vec<C::B>]), &[C::B]> {
        match &self.confl {
            Some(c) => Err(c.as_slice()),
            None => Ok((&self.props, &self.lemmas))
        }
    }
}
