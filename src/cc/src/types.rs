
use {
    smallvec::SmallVec,
    batsmt_core::{AST,backtrack},
    batsmt_solver::theory,
};

/// Boolean literal
pub type BLit = theory::BLit;

/// a small vector of `T`
pub type SVec<T> = SmallVec<[T; 3]>;

/// Builtin symbols required by the congruence closure
#[derive(Debug,Clone)]
pub struct Builtins {
    pub true_: AST,
    pub false_: AST,
    pub eq: AST,
    pub distinct: AST,
}

/// Propagation: `guard => concl`
///
/// Note that `guard` literals should all be true in current trail.
#[derive(Clone,Copy)]
pub struct Propagation<'a> {
    pub concl: BLit,
    pub guard: &'a [BLit],
}

// A propagation is represented by a pair `(idx,len)` in `self.offsets`.
// The conclusion is `self.lits[idx]` and the guard is `self.lits[idx+1 .. idx+1+len]`
/// Set of Propagations
#[derive(Clone)]
pub struct PropagationSet {
    lits: Vec<BLit>,
    offsets: Vec<(usize, usize)>, 
}

/// A conflict is a set of literals that forms a clause.
#[derive(Clone,Copy)]
pub struct Conflict<'a>(pub &'a [BLit]);

/// Interface satisfied by implementations of the congruence closure.
pub trait CCInterface : backtrack::Backtrackable {
    /// `cc.merge(t1,t2,lit)` merges `t1` and `t2` with explanation `lit`.
    fn merge(&mut self, t1: AST, t2: AST, lit: BLit);

    /// `cc.distinct(terms,lit)` asserts that all elements of `terms` are disjoint
    fn distinct(&mut self, ts: &[AST], lit: BLit);

    /// Check if the set of `merge` and `distinct` seen so far is consistent.
    ///
    /// Returns `Ok(props)` if the result is safisfiable with propagations `props`,
    /// and `Err(c)` if `c` is a valid conflict clause that contradicts
    /// the current trail.
    fn check(&mut self) -> Result<&PropagationSet, Conflict>;

    /// Description of this particular implementation
    fn impl_descr(&self) -> &'static str;
}

mod propagation {
    use super::*;

    // iterator
    struct PropIter<'a>(&'a PropagationSet, usize);

    impl PropagationSet {
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
        pub fn add_propagation(&mut self, p: Propagation) {
            let idx = self.lits.len();
            self.lits.push(p.concl);
            self.lits.extend_from_slice(p.guard);
            self.offsets.push((idx, p.guard.len()));
        }

        /// Iterate over propagations in this set.
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=Propagation<'a>> {
            PropIter(&self, 0)
        }
    }

    impl<'a> Iterator for PropIter<'a> {
        type Item = Propagation<'a>;

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
