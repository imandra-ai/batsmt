
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

/// Implementation of `Backtrackable` using a stack of invertible operations.
///
/// Note that such operations should be ready to be called several times,
/// for example in a context where operations are pushed onto the stack
/// out of order (in which case they may be undone and done again several times).
pub struct Stack<Op> {
    ops: Vec<Op>,
    levels: Vec<u32>, // we assume the stack never goes over u32
}

impl<Op> Stack<Op> {
    /// New stack.
    pub fn new() -> Self {
        Stack { ops: Vec::new(), levels: Vec::new(), }
    }

    #[inline(always)]
    pub fn n_levels(&self) -> usize { self.levels.len() }

    /// Push a backtracking point.
    ///
    /// This is useful for implementing `Backtrackable` by deferring undo
    /// actions to this `Stack`.
    pub fn push_level(&mut self) {
        let cur_size = self.ops.len();
        if cur_size > u32::MAX as usize { panic!("backtrack stack is too deep") };
        self.levels.push(cur_size as u32);
    }

    /// `stack.push(ctx,op)` pushes `op` so it's undone upon backtracking.
    ///
    /// In general, when one wants to perform some invertible action,
    /// it can be done by performing the action and immediately after
    /// pushing its undoing `Op` onto this stack.
    #[inline]
    pub fn push_undo(&mut self, op: Op) {
        self.ops.push(op);
    }

    /// Pop `n` backtracking levels, performing "undo" actions with `f`.
    ///
    /// `f` is the function that knows how to perform the "undo" operations `Op`
    /// where they are backtracked. `f` is allowed to consume the operations.
    ///
    /// This is useful for implementing `Backtrackable` by deferring undo
    /// actions to this `Stack`.
    pub fn pop_levels<F>(&mut self, n: usize, mut f: F)
        where F: FnMut(Op)
    {
        debug!("pop-levels {}", n);
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
        while self.levels.len() > offset {
            let op = self.ops.pop().unwrap();
            f(op)
        }
    }
}
