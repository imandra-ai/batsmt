
//! SAT solver Theory

use {
    std::{ops::{Deref,Not},},
    smallvec::SmallVec,
    crate::{symbol::Symbol, ast::{self,AST}, backtrack::Backtrackable},
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

/// A set of actions available to theories
pub struct Actions {
    state: ActState,
}

#[derive(Clone,Debug)]
pub(crate) enum ActState {
    Props(SVec<TheoryClause>), // propagations (new lemmas)
    Conflict(TheoryClause), // conflict reached
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
    /// By default it does nothing.
    fn partial_check(&mut self, _acts: &mut Actions, _trail: &Trail) {}
}

mod theory_lit {
    use super::*;

    impl TheoryLit {
        pub fn new(ast: AST, sign: bool) -> Self { TheoryLit::T(ast,sign) }
        pub fn new_b(ast: AST, sign: bool) -> Self { TheoryLit::BLazy(ast,sign) }
        pub fn from_blit(b: BLit) -> Self { TheoryLit::B(b) }

        pub fn is_theory(&self) -> bool { match self { TheoryLit::T(..) => true, _ => false } }
        pub fn is_pure_bool(&self) -> bool {
            match self { TheoryLit::BLazy(..) | TheoryLit::B(..) => true, _ => false }
        }
    }

    impl<S:Symbol> ast::PrettyM<S> for TheoryLit {
        fn pp_m(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            match self {
                TheoryLit::B(lit) => {
                    ctx.str(if lit.sign() {"+"} else {"-"}).string(format!("{}", lit.idx()));
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

    impl From<(AST,bool)> for TheoryLit {
        fn from(p: (AST,bool)) -> Self { Self::new(p.0,p.1) }
    }

    impl From<AST> for TheoryLit {
        fn from(t: AST) -> Self { Self::new(t, true) }
    }

    // easy negation
    impl Not for TheoryLit {
        type Output = Self;
        /// Negation on the AST-based literals
        fn not(self) -> Self {
            match self {
                TheoryLit::B(lit) => (!lit).into(),
                TheoryLit::T(t,sign) => Self::new(t, !sign),
                TheoryLit::BLazy(t,sign) => Self::new_b(t, !sign),
            }
        }
    }

    // Print a list of literals
    impl<'a, S:Symbol> ast::PrettyM<S> for &'a [TheoryLit] {
        fn pp_m(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            ctx.sexp(|ctx| {
                ctx.iter(pp::pair(" ∨", pp::space()),
                    self.iter().map(|lit| m.pp(*lit)));
            });
        }
    }
}

mod theory_clause {
    use super::*;

    impl TheoryClause {
        /// Create a clause from the given lits
        pub fn new(v: SVec<TheoryLit>) -> Self { TheoryClause{ lits: v } }

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

    impl<S:Symbol> ast::PrettyM<S> for TheoryClause {
        fn pp_m(&self, m: &M<S>, ctx: &mut pp::Ctx) { (&self).pp_m(m,ctx) }
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
        Self {state: ActState::new() }
    }

    /// Reset actions
    pub(crate) fn clear(&mut self) { self.state.clear(); }

    /// Return current state.
    #[inline(always)]
    pub(crate) fn state(&self) -> &ActState { &self.state }

    /// Instantiate the given lemma
    pub fn add_lemma(&mut self, c: &[TheoryLit]) {
        match self.state {
            ActState::Props(ref mut cs) => {
                trace!("theory.add_lemma {:?}", c);
                cs.push(c.into())
            },
            ActState::Conflict(_) => (), // ignore
        }
    }

    /// Add a conflit clause.
    ///
    /// This clause should be a valid theory lemma (a valid tautology) that
    /// is false in the current model.
    pub fn raise_conflict(&mut self, c: &[TheoryLit]) {
        // only create a conflict if there's not one already
        if let ActState::Props(_) = self.state {
            trace!("theory.raise-conflict {:?}", c);
            self.state = ActState::Conflict(c.into());
        }
    }
}

impl ActState {
    fn new() -> Self { ActState::Props(SVec::new()) }
    fn clear(&mut self) { *self = ActState::Props(SVec::new()); }
}

