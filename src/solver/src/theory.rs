
//! SAT solver Theory

use {
    std::{ops::{Deref,Not}, fmt},
    smallvec::SmallVec,
    batsmt_core::{symbol::Symbol, ast::{self,AST}, backtrack::Backtrackable},
    batsmt_pretty as pp,
};

/// A boolean literal
pub type BLit = batsat::Lit;

type SVec<T> = SmallVec<[T; 3]>;
type M<S> = ast::Manager<S>;

/// A theory-level literal, either a boolean literal, or a boolean term plus a sign.
///
/// The conversion to SAT literals of the latter
/// is done automatically and theories
/// should not have to worry about it.
#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub enum TheoryLit {
    T(AST, bool), // theory lit
    BLazy(AST, bool), // to be turned into B
    B(BLit),
}

/// A theory-level clause, such as a lemma or theory conflict
///
/// It is composed of a set of `TheoryLit`.
#[derive(Clone,Debug)]
pub struct TheoryClause {
    lits: SVec<TheoryLit>,
}

/// A temporary theory-level clause, such as a lemma or theory conflict
///
/// It is composed of a set of `TheoryLit`.
#[derive(Clone,Copy,Debug)]
pub struct TheoryClauseRef<'a> {
    lits: &'a [TheoryLit],
}

/// A set of theory clauses, with efficient append
#[derive(Clone)]
pub struct TheoryClauseSet {
    lits: Vec<TheoryLit>, // clause lits
    offsets: Vec<(usize,usize)>, // slices in `lits`
}

/// A set of actions available to theories
pub struct Actions {
    cs: TheoryClauseSet,
    conflict: bool,
    costly_conflict: bool,
}

#[derive(Clone,Debug)]
pub(crate) enum ActState<'a> {
    /// propagations (new lemmas)
    Props(&'a TheoryClauseSet),
    /// conflict reached
    Conflict {
        c: TheoryClauseRef<'a>,
        costly: bool,
    }
}

/// The theory subset of the (partial) model picked by the SAT solver.
///
/// This is given to the theory in order to check its validity. It doesn't show
/// purely boolean literals.
pub struct Trail<'a>(pub(crate) &'a [(AST,bool,BLit)]);

/// Interface satisfied by a SMT theory.
///
/// A theory is responsible for enforcing the semantics of some
/// of the boolean literals.
pub trait Theory<S:Symbol> : Backtrackable {
    /// Check a full model.
    ///
    /// ## Params:
    ///
    /// - `trail` contains triples `(term, bool, literal)` where `literal`
    ///     is `term <=> bool` and the current model contains `literal`
    /// - `acts` is a set of actions available to the theory.
    fn final_check(&mut self, acts: &mut Actions, trail: &Trail);


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
    fn partial_check(&mut self, _acts: &mut Actions, _trail: &Trail) -> bool { false }
}

mod theory_lit {
    use super::*;

    impl TheoryLit {
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
        pub fn from_blit(b: BLit) -> Self { TheoryLit::B(b) }

        /// Is is a theory literal (i.e. given to the theory when in a partial model)?
        pub fn is_theory(&self) -> bool { match self { TheoryLit::T(..) => true, _ => false } }

        /// Is it a pure boolean literal (i.e. not a theory literal)?
        pub fn is_pure_bool(&self) -> bool {
            match self { TheoryLit::BLazy(..) | TheoryLit::B(..) => true, _ => false }
        }
    }

    impl ast::PrettyM for TheoryLit {
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
    impl From<BLit> for TheoryLit {
        fn from(l: BLit) -> Self { TheoryLit::B(l) }
    }

    impl<'a,T> From<&'a T> for TheoryLit where T:Clone, TheoryLit: From<T> {
        fn from(x: &'a T) -> Self { x.clone().into() }
    }

    impl From<(AST,bool)> for TheoryLit {
        fn from(p: (AST,bool)) -> Self { Self::new_t(p.0,p.1) }
    }

    impl From<AST> for TheoryLit {
        fn from(t: AST) -> Self { Self::new_t(t, true) }
    }

    // easy negation
    impl Not for TheoryLit {
        type Output = Self;
        /// Negation on the AST-based literals
        fn not(self) -> Self {
            match self {
                TheoryLit::B(lit) => (!lit).into(),
                TheoryLit::T(t,sign) => Self::new_t(t, !sign),
                TheoryLit::BLazy(t,sign) => Self::new_b(t, !sign),
            }
        }
    }
}

mod theory_clause {
    use super::*;

    impl<'a> TheoryClauseRef<'a> {
        pub fn iter(&'a self) -> impl Iterator<Item=TheoryLit> + 'a {
            self.lits.iter().map(|l| *l)
        }
    }

    impl<'a> Deref for TheoryClauseRef<'a> {
        type Target = [TheoryLit];
        fn deref(&self) -> &Self::Target { &self.lits }
    }

    impl TheoryClause {
        /// Create a clause from the given lits
        pub fn new(v: SVec<TheoryLit>) -> Self { TheoryClause{ lits: v } }

        /// Obtain a temporary reference
        pub fn as_ref(&self) -> TheoryClauseRef {
            TheoryClauseRef{lits:&self.lits}
        }

        /// Create from a slice
        pub fn from_slice(v: &[TheoryLit]) -> Self {
            let v = v.iter().map(|x| *x).collect();
            Self::new(v)
        }

        pub fn from_iter<I, U>(i: I) -> Self
            where I : Iterator<Item=U>, U : Into<TheoryLit>
        {
            let v = i.map(|x| x.into()).collect();
            Self::new(v)
        }

        pub fn iter<'a>(&'a self) -> impl Iterator<Item=TheoryLit> + 'a {
            self.lits.iter().map(|l| *l)
        }
    }

    // Print a list of literals
    impl<'a> ast::PrettyM for TheoryClauseRef<'a> {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            ctx.sexp(|ctx| {
                ctx.iter(pp::pair(" ∨", pp::space()),
                    self.lits.iter().map(|lit| m.pp(*lit)));
            });
        }
    }

    impl ast::PrettyM for TheoryClause {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            self.as_ref().pp_m(m,ctx)
        }
    }

    impl Deref for TheoryClause {
        type Target = [TheoryLit];
        fn deref(&self) -> &Self::Target { &self.lits }
    }

    // allow to write `slice.into()`
    impl<'a> From<&'a [TheoryLit]> for TheoryClause {
        fn from(lits: &'a [TheoryLit]) -> Self {
            Self::from_slice(lits)
        }
    }

    impl<'a> From<&'a [BLit]> for TheoryClause {
        fn from(lits: &'a [BLit]) -> Self {
            Self::from_iter(lits.iter().map(|l| *l))
        }
    }
}

mod theory_clause_set {
    use super::*;

    impl TheoryClauseSet {
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
            where L: Copy + Into<TheoryLit>
        {
            let idx = self.lits.len();
            self.offsets.push((idx, c.len()));
            self.lits.extend(c.iter().map(|&x| x.into()));
        }

        /// Push a clause (as an iterator) into the set.
        pub fn push_iter<U, I>(&mut self, i: I)
            where I: Iterator<Item=U>, U: Into<TheoryLit>
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
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=TheoryClauseRef<'a>> {
            CSIter{cs: &self, idx: 0}
        }
    }

    impl fmt::Debug for TheoryClauseSet {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "clause_set(")?;
            for c in self.iter() {
                c.fmt(fmt)?
            }
            write!(fmt, ")")
        }
    }

    // iterator over clauses
    struct CSIter<'a> {
        cs: &'a TheoryClauseSet,
        idx: usize, // in `cs.offsets`
    }

    // the iterator over clauses
    impl<'a> Iterator for CSIter<'a> {
        type Item = TheoryClauseRef<'a>;

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

impl<'a> Trail<'a> {
    #[inline(always)]
    /// Access the underlying items
    pub fn as_slice(&self) -> &'a [(AST,bool,BLit)] { &self.0 }

    /// Iterate on the underlying items
    pub fn iter(&self) -> impl Iterator<Item=(AST,bool,BLit)> + 'a {
        self.0.iter().map(|&t| t)
    }

    /// Number of literals assigned
    #[inline(always)]
    pub fn len(&self) -> usize { self.0.len() }
}

impl Actions {
    /// Create a new set of actions
    pub(crate) fn new() -> Self {
        Self {
            conflict: false,
            costly_conflict: false,
            cs: TheoryClauseSet::new(),
        }
    }

    /// Reset actions
    pub(crate) fn clear(&mut self) {
        self.cs.clear();
        self.conflict = false;
        self.costly_conflict = false;
    }

    /// Return current state.
    ///
    /// Either a set of propagated clauses, or a single conflict clause
    pub(crate) fn state<'a>(&'a self) -> ActState<'a> {
        if self.conflict {
            let c = self.cs.iter().next().expect("conflict but no conflict clause");
            ActState::Conflict {c, costly: self.costly_conflict}
        } else {
            ActState::Props(&self.cs)
        }
    }

    /// Instantiate the given lemma
    pub fn add_lemma(&mut self, c: &[TheoryLit]) {
        if ! self.conflict {
            trace!("theory.add_lemma {:?}", c);
            self.cs.push(c.into())
        }
    }

    pub fn add_bool_lemma(&mut self, c: &[BLit]) {
        if ! self.conflict {
            trace!("theory.add-lemma {:?}", c);
            self.cs.push(c.into())
        }
    }

    pub fn add_lemma_iter<U, I>(&mut self, i: I)
        where I: Iterator<Item=U>, U: Into<TheoryLit>
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
    pub fn raise_conflict(&mut self, c: &[TheoryLit], costly: bool) {
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
        where I: Iterator<Item=U>, U: Into<TheoryLit>
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

