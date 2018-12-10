
use {
    std::u32,
};

/// A backtrackable component.
pub trait Backtrackable {
    type Ctx;

    /// Push one level.
    fn push_level(&mut self);

    /// Backtrack `n` levels, using `ctx` to undo changes
    fn pop_levels(&mut self, n: usize, &mut Self::Ctx);

    /// How many levels?
    fn n_levels(&self) -> usize;
}

/// An operation that can be done, then undone upon backtracking.
///
/// Note that such operations should be ready to be called several times,
/// for example in a context where operations are pushed onto the stack
/// out of order (in which case they may be undone and done again several times)
pub trait InvertibleOp {
    /// Context needed to perform the operation
    type Ctx;

    fn do_change(&mut self, &mut Self::Ctx);

    fn undo_change(&mut self, &mut Self::Ctx);
}

/// Implementation of `Backtrackable` using a stack of invertible operations
pub struct BacktrackStack<O : InvertibleOp> {
    ops: Vec<O>,
    levels: Vec<u32>, // we assume the stack never goes over u32
}

impl<O : InvertibleOp> Backtrackable for BacktrackStack<O> {
    type Ctx = O::Ctx;

    fn n_levels(&self) -> usize {
        self.levels.len()
    }

    fn push_level(&mut self) {
        let cur_size = self.ops.len();
        if cur_size > u32::MAX as usize { panic!("backtrack stack is too deep") };
        self.levels.push(cur_size as u32);
    }

    fn pop_levels(&mut self, n: usize, ctx: &mut Self::Ctx) {
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
            let mut op = self.ops.pop().unwrap();
            op.undo_change(ctx)
        }
    }

}
