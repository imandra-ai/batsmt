
pub mod cell;
pub mod stack;
pub mod hashmap;
pub mod vec;
pub mod alloc;

/// A backtrackable component.
///
/// It gets a context `Ctx` to perform operations.
pub trait Backtrackable<Ctx> {

    /// Push one level.
    fn push_level(&mut self, _c: &mut Ctx);

    /// Backtrack `n` levels, using `ctx` to undo changes
    fn pop_levels(&mut self, _c: &mut Ctx, n: usize);

    /// How many levels?
    fn n_levels(&self) -> usize;
}

pub use {
    self::cell::Ref,
    self::stack::Stack,
    self::hashmap::HashMap,
    self::vec::BVec,
    self::alloc::Alloc,
};

/// Trivial backtracking implementation, which doesn't do anything.
///
/// Defer to this if you need to implement the `Backtrackable` trait but
/// store no state.
pub struct Dummy{n_levels: usize}

impl Dummy {
    /// New stateless backtrackable object.
    pub fn new() -> Self { Dummy {n_levels: 0} }
}

impl Default for Dummy {
    fn default() -> Self { Dummy::new() }
}

impl<C> Backtrackable<C> for Dummy {
    fn push_level(&mut self, _: &mut C) { self.n_levels += 1 }
    fn pop_levels(&mut self, _: &mut C, n: usize) {
        debug_assert!(self.n_levels >= n);
        self.n_levels -= n;
    }
    fn n_levels(&self) -> usize { self.n_levels }
}
