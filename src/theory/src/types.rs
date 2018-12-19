
use {
    std::{ops::{Deref,Not}, hash::Hash, fmt},
    smallvec::SmallVec,
    batsmt_core::{symbol::Symbol, ast::{self,AST}, backtrack::Backtrackable},
    batsmt_pretty as pp,
};

/// Abstract notion of boolean literals.
///
/// A literal must be copyable, printable, comparable, hashable,
/// and have a notion of negation.
///
/// It must be the case that `!!b` is the same as `b`.
pub trait BoolLit : fmt::Debug + Eq + PartialEq + Hash + Copy + Not<Output=Self> {}

type SVec<T> = SmallVec<[T; 3]>;
type M<S> = ast::Manager<S>;

/// A theory-level literal, either a boolean literal, or a boolean term plus a sign.
///
/// The conversion to SAT literals of the latter
/// is done automatically and theories
/// should not have to worry about it.
#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub enum TheoryLit<B:BoolLit> {
    T(AST, bool), // theory lit
    BLazy(AST, bool), // to be turned into B
    B(B),
}

/// A theory-level clause, such as a lemma or theory conflict
///
/// It is composed of a set of `TheoryLit`.
#[derive(Clone,Debug)]
pub struct TheoryClause<B:BoolLit> {
    lits: SVec<TheoryLit<B>>,
}

/// A temporary theory-level clause, such as a lemma or theory conflict
///
/// It is composed of a set of `TheoryLit`.
#[derive(Clone,Copy,Debug)]
pub struct TheoryClauseRef<'a,B:BoolLit> {
    lits: &'a [TheoryLit<B>],
}

/// A set of theory clauses, with efficient append
#[derive(Clone)]
pub struct TheoryClauseSet<B:BoolLit> {
    lits: Vec<TheoryLit<B>>, // clause lits
    offsets: Vec<(usize,usize)>, // slices in `lits`
}

/// A set of actions available to theories.
///
/// A theory can use these actions to signal its caller that some
/// literals can be propagated, or that the current set of literals
/// is T-inconsistent.
pub struct Actions<B:BoolLit> {
    cs: TheoryClauseSet<B>,
    conflict: bool,
    costly_conflict: bool,
}

/// State of the `Actions` structure.
///
/// After passing some assumptions to a theory, using
/// `theory::partial_check` or `theory::final_check`, the actions
/// structure will contain
#[derive(Clone,Debug)]
pub enum ActState<'a, B:BoolLit> {
    /// propagations (new lemmas)
    Props(&'a TheoryClauseSet<B>),
    /// conflict reached
    Conflict {
        c: TheoryClauseRef<'a, B>,
        costly: bool,
    }
}

/// The theory subset of the (partial) model picked by the SAT solver.
///
/// This is given to the theory in order to check its validity. It doesn't show
/// purely boolean literals.
pub struct Trail<'a,B>(pub(crate) &'a [(AST,bool,B)]);

/// Interface satisfied by a SMT theory.
///
/// A theory is responsible for enforcing the semantics of some
/// of the boolean literals.
pub trait Theory<S:Symbol, B:BoolLit> : Backtrackable {
    /// Check a full model.
    ///
    /// ## Params:
    ///
    /// - `trail` contains triples `(term, bool, literal)` where `literal`
    ///     is `term <=> bool` and the current model contains `literal`
    /// - `acts` is a set of actions available to the theory.
    fn final_check(&mut self, acts: &mut Actions<B>, trail: &Trail<B>);

    /// Check a partial model.
    ///
    /// The parameters are similar to those of `final_check`, but
    /// this function is allowed to not fully check the model, and `trail`
    /// only contains _new_ literals (since the last call to `partial_check`).
    /// It will be called more often than `final_check` so it should be efficient.
    ///
    /// Returns: `true` if it did consider the trail, `false` otherwise.
    /// If it returns `false` then the same literals will be passed again
    /// later on (including for final check)
    ///
    /// By default it does nothing and returns `false`.
    fn partial_check(&mut self, _acts: &mut Actions<B>, _trail: &Trail<B>) -> bool { false }
}

mod theory_lit {
    use super::*;

    impl<B:BoolLit> TheoryLit<B> {
        /// Make a theory literal.
        ///
        /// This literal will map bidirectionally with the term, and
        /// will be passed to the Theory whenever it's decided by the SAT solver.
        pub fn new_t(ast: AST, sign: bool) -> Self { TheoryLit::T(ast,sign) }

        /// Make a lazy pure boolean literal.
        ///
        /// This designates a pure boolean literal that will live in the SAT
        /// solver but will not be passed to the theory.
        /// The same term will always map to the same boolean literal.
        pub fn new_b(ast: AST, sign: bool) -> Self { TheoryLit::BLazy(ast,sign) }

        /// Wrap a pure boolean literal.
        ///
        /// This pure SAT literal will never be passed to the theory.
        /// It is given to the SAT solver as is.
        pub fn from_blit(b: B) -> Self { TheoryLit::B(b) }

        /// Is is a theory literal (i.e. given to the theory when in a partial model)?
        pub fn is_theory(&self) -> bool { match self { TheoryLit::T(..) => true, _ => false } }

        /// Is it a pure boolean literal (i.e. not a theory literal)?
        pub fn is_pure_bool(&self) -> bool {
            match self { TheoryLit::BLazy(..) | TheoryLit::B(..) => true, _ => false }
        }
    }

    impl<B:BoolLit> ast::PrettyM for TheoryLit<B> {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            match self {
                TheoryLit::B(lit) => {
                    pp::Pretty::pp(&pp::dbg(lit), ctx);
                },
                TheoryLit::T(t,sign) => {
                    let s = if *sign { "t+" } else { "t-" };
                    ctx.sexp(|ctx| {
                        ctx.str(s).space().pp(&m.pp(*t));
                    });
                },
                TheoryLit::BLazy(t,sign) => {
                    let s = if *sign { "b+" } else { "b-" };
                    ctx.sexp(|ctx| {ctx.str(s).space().pp(&m.pp(*t)); });
                },
            }
        }
    }

    // conversion from BLit
    impl<B:BoolLit> From<B> for TheoryLit<B> {
        fn from(l: B) -> Self { TheoryLit::B(l) }
    }

    impl<B:BoolLit> From<(AST,bool)> for TheoryLit<B> {
        fn from(p: (AST,bool)) -> Self { Self::new_t(p.0,p.1) }
    }

    impl<B:BoolLit> From<AST> for TheoryLit<B> {
        fn from(t: AST) -> Self { Self::new_t(t, true) }
    }

    // easy negation
    impl<B:BoolLit> Not for TheoryLit<B> {
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

    impl<'a,B:BoolLit> TheoryClauseRef<'a,B> {
        pub fn iter(&'a self) -> impl Iterator<Item=TheoryLit<B>> + 'a {
            self.lits.iter().map(|l| *l)
        }
    }

    impl<'a,B:BoolLit> Deref for TheoryClauseRef<'a,B> {
        type Target = [TheoryLit<B>];
        fn deref(&self) -> &Self::Target { &self.lits }
    }

    impl<B:BoolLit> TheoryClause<B> {
        /// Create a clause from the given lits
        pub fn new(v: SVec<TheoryLit<B>>) -> Self { TheoryClause{ lits: v } }

        /// Obtain a temporary reference
        pub fn as_ref(&self) -> TheoryClauseRef<B> {
            TheoryClauseRef{lits:&self.lits}
        }

        /// Create from a slice
        pub fn from_slice(v: &[TheoryLit<B>]) -> Self {
            let v = v.iter().map(|x| *x).collect();
            Self::new(v)
        }

        pub fn from_iter<I, U>(i: I) -> Self
            where I : Iterator<Item=U>, U : Into<TheoryLit<B>>
        {
            let v = i.map(|x| x.into()).collect();
            Self::new(v)
        }

        pub fn iter<'a>(&'a self) -> impl Iterator<Item=TheoryLit<B>> + 'a {
            self.lits.iter().map(|l| *l)
        }
    }

    // Print a list of literals
    impl<'a,B:BoolLit> ast::PrettyM for TheoryClauseRef<'a,B> {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            ctx.sexp(|ctx| {
                ctx.iter(pp::pair(" ∨", pp::space()),
                    self.lits.iter().map(|lit| m.pp(*lit)));
            });
        }
    }

    impl<B:BoolLit> ast::PrettyM for TheoryClause<B> {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            self.as_ref().pp_m(m,ctx)
        }
    }

    impl<B:BoolLit> Deref for TheoryClause<B> {
        type Target = [TheoryLit<B>];
        fn deref(&self) -> &Self::Target { &self.lits }
    }

    // allow to write `slice.into()`
    impl<'a,B:BoolLit> From<&'a [TheoryLit<B>]> for TheoryClause<B> {
        fn from(lits: &'a [TheoryLit<B>]) -> Self {
            Self::from_slice(lits)
        }
    }

    impl<'a,B:BoolLit> From<&'a [B]> for TheoryClause<B> {
        fn from(lits: &'a [B]) -> Self {
            Self::from_iter(lits.iter().map(|l| l.clone()))
        }
    }
}

mod theory_clause_set {
    use super::*;

    impl<B:BoolLit> TheoryClauseSet<B> {
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
            where L: Copy + Into<TheoryLit<B>>
        {
            let idx = self.lits.len();
            self.offsets.push((idx, c.len()));
            self.lits.extend(c.iter().map(|&x| x.into()));
        }

        /// Push a clause (as an iterator) into the set.
        pub fn push_iter<U, I>(&mut self, i: I)
            where I: Iterator<Item=U>, U: Into<TheoryLit<B>>
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
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=TheoryClauseRef<'a,B>> {
            CSIter{cs: &self, idx: 0}
        }
    }

    impl<B:BoolLit> fmt::Debug for TheoryClauseSet<B> {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "clause_set(")?;
            for c in self.iter() {
                c.fmt(fmt)?
            }
            write!(fmt, ")")
        }
    }

    // iterator over clauses
    struct CSIter<'a,B:BoolLit> {
        cs: &'a TheoryClauseSet<B>,
        idx: usize, // in `cs.offsets`
    }

    // the iterator over clauses
    impl<'a,B:BoolLit> Iterator for CSIter<'a,B> {
        type Item = TheoryClauseRef<'a,B>;

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
}

impl<'a,B:BoolLit> Trail<'a,B> {
    #[inline(always)]
    /// Access the underlying items.
    pub fn as_slice(&self) -> &'a [(AST,bool,B)] { &self.0 }

    #[inline(always)]
    /// Build a trail from this slice.
    pub fn from_slice(a: &'a [(AST,bool,B)]) -> Self { Trail(a) }

    /// Iterate on the underlying items.
    pub fn iter(&self) -> impl Iterator<Item=(AST,bool,B)> + 'a {
        self.0.iter().map(|&t| t)
    }

    /// Number of literals assigned.
    #[inline(always)]
    pub fn len(&self) -> usize { self.0.len() }
}

impl<B:BoolLit> Actions<B> {
    /// Create a new set of actions
    pub fn new() -> Self {
        Self {
            conflict: false,
            costly_conflict: false,
            cs: TheoryClauseSet::new(),
        }
    }

    /// Reset actions
    pub fn clear(&mut self) {
        self.cs.clear();
        self.conflict = false;
        self.costly_conflict = false;
    }

    /// Return current state.
    ///
    /// Either a set of propagated clauses, or a single conflict clause
    pub fn state<'a>(&'a self) -> ActState<'a,B> {
        if self.conflict {
            let c = self.cs.iter().next().expect("conflict but no conflict clause");
            ActState::Conflict {c, costly: self.costly_conflict}
        } else {
            ActState::Props(&self.cs)
        }
    }

    /// Instantiate the given lemma
    pub fn add_lemma(&mut self, c: &[TheoryLit<B>]) {
        if ! self.conflict {
            trace!("theory.add_lemma {:?}", c);
            self.cs.push(c.into())
        }
    }

    pub fn add_bool_lemma(&mut self, c: &[B]) {
        if ! self.conflict {
            trace!("theory.add-lemma {:?}", c);
            self.cs.push(c.into())
        }
    }

    pub fn add_lemma_iter<U, I>(&mut self, i: I)
        where I: Iterator<Item=U>, U: Into<TheoryLit<B>>
    {
        if ! self.conflict {
            trace!("theory.add-lemma-iter");
            self.cs.push_iter(i);
        }
    }

    /// Add a conflit clause.
    ///
    /// This clause should be a valid theory lemma (a valid tautology) that
    /// is false in the current model.
    pub fn raise_conflict(&mut self, c: &[TheoryLit<B>], costly: bool) {
        // only create a conflict if there's not one already
        if ! self.conflict {
            trace!("theory.raise-conflict {:?} (costly: {})", c, costly);
            self.conflict = true;
            self.costly_conflict = costly;
            self.cs.clear(); // remove propagated lemmas
            self.cs.push(c);
        }
    }

    /// Add a conflict clause.
    ///
    /// The clause is built from an iterator over theory lits
    pub fn raise_conflict_iter<U, I>(&mut self, i: I, costly: bool)
        where I: Iterator<Item=U>, U: Into<TheoryLit<B>>
    {
        if ! self.conflict {
            trace!("theory.raise-conflict-iter (costly: {})", costly);
            self.conflict = true;
            self.costly_conflict = costly;
            self.cs.clear(); // remove propagated lemmas
            self.cs.push_iter(i);
        }
    }
}

/// A basic implementation of boolean literals using signed integers
pub mod int_lit {
    /// A very simple representation of literals using signed integers.
    ///
    /// It doesn't correspond to any solver, but can be useful for testing.
    #[derive(Copy,Clone,Eq,PartialEq,Hash,Debug)]
    pub struct Lit(i32);

    impl std::ops::Not for Lit {
        type Output = Lit;
        fn not(self) -> Self { debug_assert_ne!(self.0, 0); Lit(-self.0) }
    }

    impl super::BoolLit for Lit {}
}
