
//! SAT solver Theory

use {
    smallvec::SmallVec,
    crate::{symbol::Symbol, ast::{self,AST}, backtrack::Backtrackable},
};

/// A boolean literal
pub use batsat::Lit as BLit;

type SVec<T> = SmallVec<[T; 3]>;

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
    /// Concrete initialization function.
    ///
    /// The theory receives a term manager.
    fn init(m: ast::Manager<S>) -> Self where Self : Sized;

    /// Check a partial model.
    ///
    /// ## Params:
    ///
    /// - `i` iterates over triples `(term, bool, literal)` where `literal`
    ///     is `term <=> bool`
    /// - `acts` is a set of actions available to the theory.
    fn final_check<I>(&mut self, acts: &mut Actions, i: I)
        where I: Iterator<Item=(AST, bool, BLit)>;
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
