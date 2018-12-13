
//! SAT solver Theory

use {
    smallvec::SmallVec,
    crate::{symbol::Symbol, ast::AST, backtrack::Backtrackable},
    batsmt_pretty as pp,
};

/// A boolean literal
pub type BLit = batsat::Lit;

type SVec<T> = SmallVec<[T; 3]>;

/// A theory-level literal, either a boolean literal, or a boolean term plus a sign.
///
/// The conversion to SAT literals of the latter
/// is done automatically and theories
/// should not have to worry about it.
#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub enum TheoryLit {
    T(AST, bool),
    B(BLit),
}

/// A theory-level clause, such as a lemma or theory conflict
///
/// It is composed of a set of `TheoryLit`.
#[derive(Clone)]
pub struct TheoryClause {
    lits: SVec<TheoryLit>,
}

/// A set of actions available to theories
pub struct Actions {
    state: ActState,
}

#[derive(Clone,Debug)]
enum ActState {
    Props(SVec<Vec<AST>>), // propagations
    Conflict(SVec<AST>), // conflict reached
}

/// Interface satisfied by a SMT theory.
///
/// A theory is responsible for enforcing the semantics of some
/// of the boolean literals.
pub trait Theory<S:Symbol> : Backtrackable {
    /// Check a full model.
    ///
    /// ## Params:
    ///
    /// - `i` iterates over triples `(term, bool, literal)` where `literal`
    ///     is `term <=> bool`
    /// - `acts` is a set of actions available to the theory.
    fn final_check<I>(&mut self, acts: &mut Actions, i: I)
        where I: Iterator<Item=(AST, bool, BLit)>;


    /// Check a partial model.
    ///
    /// The parameters are similar to those of `final_check`, but
    /// this function is allowed to not fully check the model.
    /// It will be called more often than `final_check` so it should be efficient.
    ///
    /// By default it does nothing.
    fn partial_check<I>(&mut self, _acts: &mut Actions, _i: I)
        where I: Iterator<Item=(AST, bool, BLit)>
    {}
}

impl Actions {
    /// Create a new set of actions
    pub(crate) fn new() -> Self {
        Self {state: ActState::new() }
    }

    /// Reset actions
    pub(crate) fn clear(&mut self) { self.state.clear(); }

    /// Instantiate the given lemma
    pub fn add_lemma(&mut self, c: &[AST]) {
        match self.state {
            ActState::Props(ref mut cs) => {
                debug!("theory.add_lemma {:?}", c);
                let v = c.iter().map(|t| *t).collect();
                cs.push(v)
            },
            ActState::Conflict(_) => (), // ignore
        }
    }

    /// Add a conflit clause.
    ///
    /// This clause should be a valid theory lemma (a valid tautology) that
    /// is false in the current model.
    pub fn raise_conflict(&mut self, c: &[AST]) {
        // only create a conflict if there's not one already
        if let ActState::Props(_) = self.state {
            debug!("theory.raise-conflict {:?}", c);
            let c = c.iter().map(|t| *t).collect();
            self.state = ActState::Conflict(c);
        }
    }
}

impl ActState {
    fn new() -> Self { ActState::Props(SVec::new()) }
    fn clear(&mut self) { *self = ActState::Props(SVec::new()); }
}

/* FIXME: implem of pretty + `debug` and `display` methods
impl<'a> pretty::Pretty for (&'a ast::Manager, &'a TheoryClause) {

}
*/
