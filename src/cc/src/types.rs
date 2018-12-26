
use {
    smallvec::SmallVec,
};

pub use batsmt_theory::{Ctx, BoolLit, };

/// a small vector of `T`
pub type SVec<T> = SmallVec<[T; 3]>;

/// Builtin symbols required by the congruence closure
#[derive(Debug,Clone)]
pub struct Builtins<AST:Clone> {
    pub true_: AST,
    pub false_: AST,
    pub not_: AST,
    pub eq: AST,
    pub distinct: AST,
}

/// Set of Propagations.
#[derive(Clone)]
pub struct PropagationSet<B> {
    lits: Vec<B>,
}

/// A conflict is a set of literals that forms a clause.
#[derive(Clone,Copy)]
pub struct Conflict<'a,B>(pub &'a [B]);

mod propagation {
    use super::*;

    // iterator
    struct PropIter<'a,C:Ctx>(&'a PropagationSet<C::B>, usize);

    impl<B:BoolLit> PropagationSet<B> {
        /// New propagation set.
        pub fn new() -> Self { PropagationSet { lits: vec!(), } }

        /// Number of elements in the set
        #[inline(always)]
        pub fn len(&self) -> usize { self.lits.len() }

        /// Clear internal content
        #[inline(always)]
        pub fn clear(&mut self) {
            self.lits.clear();
        }

        /// Add a propagation to the set.
        #[inline(always)]
        pub fn propagate(&mut self, p: B) {
            self.lits.push(p);
        }

        /// Iterate over propagations in this set.
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=B> + 'a {
            self.lits.iter().cloned()
        }
    }
}
