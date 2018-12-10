
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

/// Trivial backtracking state
pub struct Stateless{n_levels: usize}

impl Stateless {
    /// New stateless backtrackable object
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

/// How to perform an operation, and how to undo it
pub trait PerformOp<Op> {
    fn do_op(&mut self, op: &mut Op);
    fn undo_op(&mut self, op: &mut Op);
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
    pub fn new() -> Self {
        Stack { ops: Vec::new(), levels: Vec::new(), }
    }
}

impl<Op> Stack<Op> {
    /// `stack.push(ctx,op)` performs `op`, and will undo it upon backtracking.
    ///
    /// In general, when one wants to perform some invertible action, using
    /// this stack and performing the change via an `O` value is a good move.
    pub fn push<Ctx>(&mut self, ctx: &mut Ctx, mut op: Op)
        where Ctx : PerformOp<Op> 
    {
        ctx.do_op(&mut op);
        self.ops.push(op);
    }

    /// Promote into a stack with context
    #[inline(always)]
    pub fn promote<'a, Ctx>(&'a mut self, ctx: &'a mut Ctx)
        -> impl Backtrackable + 'a
        where Ctx: PerformOp<Op>
    { (self, ctx) }

    #[inline(always)]
    pub fn n_levels(&self) -> usize { self.levels.len() }
}

impl<'a, Ctx, Op> Backtrackable for (&mut Stack<Op>, &'a mut Ctx)
    where Ctx : PerformOp<Op>
{
    #[inline(always)]
    fn n_levels(&self) -> usize { self.0.n_levels() }

    fn push_level(&mut self) {
        let cur_size = self.0.ops.len();
        if cur_size > u32::MAX as usize { panic!("backtrack stack is too deep") };
        self.0.levels.push(cur_size as u32);
    }

    fn pop_levels(&mut self, n: usize) {
        debug!("pop-levels {}", n);
        if n > self.0.levels.len() {
            panic!("cannot backtrack {} levels in a stack with only {}", n, self.0.levels.len());
        }
        // obtain offset in `self.ops` and resize the `levels` stack
        let offset = {
            let idx = self.0.levels.len() - n;
            let offset = self.0.levels[idx];
            self.0.levels.resize(idx, 0);
            offset as usize
        };
        while self.0.levels.len() > offset {
            let mut op = self.0.ops.pop().unwrap();
            self.1.undo_op(&mut op)
        }
    }

}
