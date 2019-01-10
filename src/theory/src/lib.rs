
//! General notion of Theory.
//!
//! A theory can decide conjunctions of atoms that belong to some fragment of terms.
//! It is backtrackable (following the SAT solver).
//!
//! Such a theory should be usable to implement a CDCL(T) solver (see `batsmt-solver`),
//! on its own for contextual simplification, or with some other boolean
//! enumerator such as a BDD.
//! For this reason, it abstracts over the type of boolean literals (`BoolLit`).

#[macro_use] extern crate log;

use {
    std::{ops::{Deref,Not}, hash::Hash, fmt},
    batsmt_core::{ backtrack::Backtrackable, ast, ast_u32, gc, },
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

/// A theory is parametrized by a `HManager` (with its AST, symbol, etc.) and boolean literals.
pub trait Ctx : ast_u32::ManagerU32 + BoolLitCtx {}

// auto impl
impl<T> Ctx for T
    where T : ast_u32::ManagerU32,
          T : BoolLitCtx,
          T : pp::Pretty1<ast_u32::AST> {}

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

/// A temporary theory-level clause, such as a lemma or theory conflict
///
/// It is composed of a set of `TheoryLit`.
#[derive(Clone,Copy)]
pub struct TheoryClauseRef<'a,C:Ctx> {
    lits: &'a [TheoryLit<C>],
}

/// A set of theory clauses, with efficient append
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
pub struct Actions<C:Ctx> {
    cs: TheoryClauseSet<C>,
    propagations: Vec<C::B>,
    conflict: bool,
    costly_conflict: bool,
    stats: Stats,
}

/// State of the `Actions` structure.
///
/// After passing some assumptions to a theory, using
/// `theory::partial_check` or `theory::final_check`, the actions
/// structure will contain
#[derive(Clone,Debug)]
pub enum ActState<'a, C:Ctx> {
    /// propagations and new lemmas
    Props {
        props: &'a [C::B],
        lemmas: &'a TheoryClauseSet<C>
    },
    /// conflict reached
    Conflict {
        c: TheoryClauseRef<'a, C>,
        costly: bool,
    }
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
    fn final_check(&mut self, _ctx: &mut C, acts: &mut Actions<C>, trail: &Trail<C>);

    /// Check a partial model.
    ///
    /// This is only called if `self.has_partial_check()` is `true`.
    ///
    /// The parameters are similar to those of `final_check`, but
    /// this function is allowed to not fully check the model, and `trail`
    /// only contains _new_ literals (since the last call to `partial_check`).
    /// It will be called more often than `final_check` so it should be efficient.
    fn partial_check(&mut self, _ctx: &mut C, _acts: &mut Actions<C>, _trail: &Trail<C>) {}

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
    conflicts: u64,
    propagations: u64,
    lemmas: u64,
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
        fn pp_with(&self, c: &C, ctx: &mut pp::Ctx) {
            match self {
                TheoryLit::B(lit) => {
                    pp::Pretty::pp_into(&pp::dbg(lit), ctx);
                },
                TheoryLit::T(t,sign) => {
                    let s = if *sign { "t+" } else { "t-" };
                    ctx.sexp(|ctx| {
                        ctx.str(s).space().pp(&ast::pp(c,t));
                    });
                },
                TheoryLit::BLazy(t,sign) => {
                    let s = if *sign { "b+" } else { "b-" };
                    ctx.sexp(|ctx| {ctx.str(s).space().pp(&ast::pp(c,t)); });
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
        fn pp_with(&self, c: &C, ctx: &mut pp::Ctx) {
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
    pub fn iter(&self) -> impl Iterator<Item=(ast_u32::AST,bool,C::B)> + 'a {
        self.0.iter().cloned()
    }

    /// Number of literals assigned.
    #[inline(always)]
    pub fn len(&self) -> usize { self.0.len() }
}

impl<C:Ctx> Actions<C> {
    /// Create a new set of actions
    pub fn new() -> Self {
        Self {
            conflict: false,
            costly_conflict: false,
            stats: Stats::new(),
            propagations: vec!(),
            cs: TheoryClauseSet::new(),
        }
    }

    /// Reset actions
    pub fn clear(&mut self) {
        self.cs.clear();
        self.propagations.clear();
        self.conflict = false;
        self.costly_conflict = false;
    }

    /// Return current state.
    ///
    /// Either a set of propagated clauses, or a single conflict clause
    pub fn state<'a>(&'a self) -> ActState<'a, C> {
        if self.conflict {
            let c = self.cs.iter().next().expect("conflict but no conflict clause");
            ActState::Conflict {c, costly: self.costly_conflict}
        } else {
            ActState::Props{
                props: &self.propagations,
                lemmas: &self.cs
            }
        }
    }

    pub fn is_sat(&self) -> bool { ! self.conflict }
    pub fn is_unsat(&self) -> bool { self.conflict }

    /// Propagate the given boolean literal.
    #[inline(always)]
    pub fn propagate(&mut self, p: C::B) {
        if ! self.conflict {
            self.propagations.push(p);
            self.stats.propagations += 1;
        }
    }

    /// Instantiate the given lemma
    pub fn add_lemma(&mut self, c: &[TheoryLit<C>]) {
        if ! self.conflict {
            trace!("theory.add_lemma {:?}", c);
            self.cs.push(c.into());
            self.stats.lemmas += 1;
        }
    }

    pub fn add_bool_lemma(&mut self, c: &[C::B]) {
        if ! self.conflict {
            trace!("theory.add-lemma {:?}", c);
            let i = c.iter().map(|a| TheoryLit::from_blit(*a));
            self.cs.push_iter(i);
            self.stats.lemmas += 1;
        }
    }

    pub fn add_lemma_iter<U, I>(&mut self, i: I)
        where I: Iterator<Item=U>, U: Into<TheoryLit<C>>
    {
        if ! self.conflict {
            trace!("theory.add-lemma-iter");
            self.cs.push_iter(i);
            self.stats.lemmas += 1;
        }
    }

    /// Add a conflit clause.
    ///
    /// This clause should be a valid theory lemma (a valid tautology) that
    /// is false in the current model.
    pub fn raise_conflict(&mut self, c: &[TheoryLit<C>], costly: bool) {
        // only create a conflict if there's not one already
        if ! self.conflict {
            trace!("theory.raise-conflict {:?} (costly: {})", c, costly);
            self.conflict = true;
            self.costly_conflict = costly;
            self.propagations.clear();
            self.cs.clear(); // remove propagated lemmas
            self.cs.push(c);
            self.stats.conflicts += 1;
        }
    }

    /// Add a conflict clause.
    ///
    /// The clause is built from an iterator over theory lits
    pub fn raise_conflict_iter<U, I>(&mut self, i: I, costly: bool)
        where I: Iterator<Item=U>, U: Into<TheoryLit<C>>
    {
        if ! self.conflict {
            trace!("theory.raise-conflict-iter (costly: {})", costly);
            self.conflict = true;
            self.costly_conflict = costly;
            self.propagations.clear();
            self.cs.clear(); // remove propagated lemmas
            self.cs.push_iter(i);
            self.stats.conflicts += 1;
        }
    }

    /// Access statistics.
    pub fn stats(&self) -> &Stats { &self.stats }
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
