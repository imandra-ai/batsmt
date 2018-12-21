
use {
    smallvec::SmallVec,
    batsmt_core::{AST,backtrack},
};

pub use batsmt_theory::BoolLit;

/// a small vector of `T`
pub type SVec<T> = SmallVec<[T; 3]>;

/// Builtin symbols required by the congruence closure
#[derive(Debug,Clone)]
pub struct Builtins {
    pub true_: AST,
    pub false_: AST,
    pub not_: AST,
    pub eq: AST,
    pub distinct: AST,
}

/// Propagation: `guard => concl`
///
/// Note that `guard` literals should all be true in current trail.
#[derive(Clone,Copy)]
pub struct Propagation<'a,B:BoolLit> {
    pub concl: B,
    pub guard: &'a [B],
}

// A propagation is represented by a pair `(idx,len)` in `self.offsets`.
// The conclusion is `self.lits[idx]` and the guard is `self.lits[idx+1 .. idx+1+len]`
/// Set of Propagations
#[derive(Clone)]
pub struct PropagationSet<B> {
    lits: Vec<B>,
    offsets: Vec<(usize, usize)>,
}

/// A conflict is a set of literals that forms a clause.
#[derive(Clone,Copy)]
pub struct Conflict<'a,B>(pub &'a [B]);

mod propagation {
    use super::*;

    // iterator
    struct PropIter<'a,B:BoolLit>(&'a PropagationSet<B>, usize);

    impl<B:BoolLit> PropagationSet<B> {
        /// New propagation set.
        pub fn new() -> Self {
            PropagationSet { lits: vec!(), offsets: vec!(), }
        }

        /// Number of elements in the set
        pub fn len(&self) -> usize { self.offsets.len() }

        /// Clear internal content
        pub fn clear(&mut self) {
            self.lits.clear();
            self.offsets.clear();
        }

        /// Add a propagation to the set.
        pub fn add_propagation(&mut self, p: Propagation<B>) {
            let idx = self.lits.len();
            self.lits.push(p.concl);
            self.lits.extend_from_slice(p.guard);
            self.offsets.push((idx, p.guard.len()));
        }

        pub fn propagate(&mut self, concl: B, guard: &[B]) {
            let prop = Propagation {concl, guard};
            self.add_propagation(prop)
        }

        /// Iterate over propagations in this set.
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=Propagation<'a,B>> {
            PropIter(&self, 0)
        }
    }

    impl<'a,B:BoolLit> Iterator for PropIter<'a,B> {
        type Item = Propagation<'a,B>;

        fn next(&mut self) -> Option<Self::Item> {
            if self.1 >= self.0.offsets.len() {
                None
            } else {
                let (idx,len) = self.0.offsets[self.1];
                self.1 += 1;
                let concl = self.0.lits[idx];
                let guard = &self.0.lits[idx+1 .. idx+1+len];
                Some(Propagation {concl, guard})
            }
        }
    }

}
