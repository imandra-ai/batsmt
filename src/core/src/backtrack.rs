
use {
    std::{
        u32,
    }, 
};

/// A backtrackable component.
pub trait Backtrackable {
    /// Push one level.
    fn push_level(&mut self);

    /// Backtrack `n` levels, using `ctx` to undo changes
    fn pop_levels(&mut self, n: usize);

    /// How many levels?
    fn n_levels(&self) -> usize;
}

/// Trivial backtracking implementation, which doesn't do anything.
///
/// Defer to this if you need to implement the `Backtrackable` trait but
/// store no state.
pub struct Stateless{n_levels: usize}

impl Stateless {
    /// New stateless backtrackable object.
    pub fn new() -> Self { Stateless {n_levels: 0} }
}

impl Default for Stateless {
    fn default() -> Self { Stateless::new() }
}

impl Backtrackable for Stateless {
    fn push_level(&mut self) { self.n_levels += 1 }
    fn pop_levels(&mut self, n: usize) {
        debug_assert!(self.n_levels >= n);
        self.n_levels -= n;
    }
    fn n_levels(&self) -> usize { self.n_levels }
}

/// A stack of items that support backtrack-able `push`.
///
/// This can be used to push "undo" operations when mutating a structure
/// in a backtrackable context. The `pop_levels` function should be called
/// with a function `f` that will undo the modifications.
///
/// It can also be used as a normal stack of objects where `push` is undone
/// upon backtracking.
pub struct Stack<T> {
    st: Vec<T>,
    levels: Vec<u32>, // we assume the stack never goes over u32
}

impl<T> Stack<T> {
    /// New stack.
    pub fn new() -> Self {
        Stack { st: Vec::new(), levels: Vec::new(), }
    }

    #[inline(always)]
    pub fn n_levels(&self) -> usize { self.levels.len() }

    /// Push a backtracking point.
    ///
    /// This is useful for implementing `Backtrackable` by deferring undo
    /// actions to this `Stack`.
    pub fn push_level(&mut self) {
        let cur_size = self.st.len();
        if cur_size > u32::MAX as usize { panic!("backtrack stack is too deep") };
        self.levels.push(cur_size as u32);
    }

    /// `stack.push(ctx,x)` pushes `x` onto the stack.
    ///
    /// `x` will be pop'd upon backtracking, and some function called on it.
    ///
    /// In general, when one wants to perform some invertible action,
    /// it can be done by performing the action and immediately after
    /// pushing its undoing `T` onto this stack.
    #[inline(always)]
    pub fn push(&mut self, x: T) {
        self.st.push(x);
    }

    /// Pop `n` backtracking levels, performing "undo" actions with `f`.
    ///
    /// `f` is the function that knows how to perform the "undo" operations `Op`
    /// where they are backtracked. `f` is allowed to consume the operations.
    ///
    /// This is useful for implementing `Backtrackable` by deferring undo
    /// actions to this `Stack`.
    pub fn pop_levels<F>(&mut self, n: usize, mut f: F)
        where F: FnMut(T)
    {
        if n > self.levels.len() {
            panic!("cannot backtrack {} levels in a stack with only {}", n, self.levels.len());
        }
        // obtain offset in `self.ops` and resize the `levels` stack
        let offset = {
            let idx = self.levels.len() - n;
            let offset = self.levels[idx];
            self.levels.resize(idx, 0);
            offset as usize
        };
        while self.st.len() > offset {
            let op = self.st.pop().unwrap();
            f(op)
        }
    }

    /// Iterate over the items in the stack.
    #[inline(always)]
    pub fn iter(&self) -> impl Iterator<Item=&T> {
        self.st.iter()
    }

    /// Immutable view into the internal operations
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        &self.st
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_stack() {
        let mut s = Stack::new();

        s.push(0);
        s.push_level();
        assert_eq!(s.n_levels(), 1);
        assert_eq!(s.as_slice(), &[0]);

        s.push(1);
        s.push(2);

        assert_eq!(s.as_slice(), &[0,1,2]);

        s.push_level();
        assert_eq!(s.n_levels(), 2);
        assert_eq!(s.as_slice(), &[0,1,2]);

        s.push(3);
        assert_eq!(s.as_slice(), &[0,1,2,3]);

        s.pop_levels(2, |x| { assert!(x > 0) });
        assert_eq!(s.n_levels(), 0);
        assert_eq!(s.as_slice(), &[0]);

        s.push_level();

        s.push(1);
        s.push(2);

        s.push_level();
        assert_eq!(s.n_levels(), 2);
        assert_eq!(s.as_slice(), &[0,1,2]);

        s.push(3);
        s.push(4);
        assert_eq!(s.as_slice(), &[0,1,2,3,4]);

        s.pop_levels(1, |x| { assert!(x >= 3) });
        assert_eq!(s.n_levels(), 1);
        assert_eq!(s.as_slice(), &[0,1,2]);

        s.pop_levels(1, |x| { assert!(x > 0) });
        assert_eq!(s.n_levels(), 0);
        assert_eq!(s.as_slice(), &[0]);
    }
}
