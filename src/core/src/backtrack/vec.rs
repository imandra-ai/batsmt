
//! Backtrackable vector.

use {
    crate::gc::HasInternalMemory,
    super::Stack as BStack,
};

/// Backtackable vector of `T`.
pub struct BVec<T:Clone>{
    v: Vec<T>,
    undo: BStack<UndoOp<T>>,
}

// what to do on backtrack
#[derive(Clone)]
enum UndoOp<T> {
    Pop(usize), // pop n-th element
    Set(usize, T),
}

impl<T:Clone> BVec<T> {
    /// New backtrackable vector.
    pub fn new() -> Self {
        BVec { v: vec!(), undo: BStack::new() }
    }

    /// Push a new element into the vector.
    #[inline]
    pub fn push(&mut self, x: T) {
        let len = self.v.len();
        self.v.push(x);
        self.undo.push_if_nonzero(UndoOp::Pop(len));
    }

    /// Push a new element into the vector. This will not be backtracked.
    #[inline]
    pub fn push_nonbacktrack(&mut self, x: T) {
        self.v.push(x);
    }

    /// Length of the vector.
    #[inline(always)]
    pub fn len(&self) -> usize { self.v.len() }

    /// Access `i`-th element.
    ///
    /// ## Safety
    /// panics if `i` is out of bounds.
    pub fn get(&self, i: usize) -> &T {
        &self.v[i]
    }

    /// Modify `i`-th element.
    ///
    /// The previous element will be saved.
    ///
    /// ## Safety
    /// panics if `i` is out of bounds.
    pub fn set(&mut self, i: usize, x: T) {
        if self.undo.n_levels() > 0 {
            // save previous value
            self.undo.push(UndoOp::Set(i, self.v[i].clone()));
        }
        self.v[i] = x;
    }

    #[inline(always)]
    pub fn n_levels(&self) -> usize { self.undo.n_levels() }

    #[inline(always)]
    pub fn push_level(&mut self) {
        self.undo.push_level()
    }

    /// Backtrack `n` levels.
    pub fn pop_levels(&mut self, n: usize) {
        if n > self.undo.n_levels() {
            panic!("cannot backtrack that many levels");
        }

        let BVec {undo, v} = self;
        // perform undo operations
        undo.pop_levels(n, |op| {
            match op {
                UndoOp::Pop(n) => {
                    if n+1 == v.len() {
                        v.pop(); // last element
                    } else {
                        v.remove(n);
                    }
                },
                UndoOp::Set(i,x) => {
                    v[i] = x;
                },
            }

        });
    }
}

impl<T:Clone+Eq> BVec<T> {
    /// Update `i`-th element using `f`.
    ///
    /// The previous element will be saved if distinct, and the result of `f` returned.
    ///
    /// ## Safety
    /// panics if `i` is out of bounds.
    pub fn update<F,R>(&mut self, i: usize, f: F) -> R
        where F: FnOnce(&mut T) -> R
    {
        let cur_elt = &mut self.v[i];

        let mut new_elt = cur_elt.clone();
        let res = f(&mut new_elt);

        if self.undo.n_levels() > 0 && *cur_elt != new_elt {
            // save previous value, if different
            std::mem::swap(cur_elt, &mut new_elt);
            // `new_elt` now contains the old value.
            self.undo.push(UndoOp::Set(i, new_elt));
        }
        res
    }
}

impl<T:Clone> std::ops::Index<usize> for BVec<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, i: usize) -> &Self::Output {
        self.get(i)
    }
}

impl<T:Clone> HasInternalMemory for BVec<T> {
    fn reclaim_unused_memory(&mut self) {
        self.v.shrink_to_fit();
        self.undo.reclaim_unused_memory();
    }
}
