
use std::u32;

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
