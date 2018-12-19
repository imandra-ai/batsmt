
pub mod cell;
pub mod stack;
pub mod hashmap;

/// A backtrackable component.
pub trait Backtrackable {
    /// Push one level.
    fn push_level(&mut self);

    /// Backtrack `n` levels, using `ctx` to undo changes
    fn pop_levels(&mut self, n: usize);

    /// How many levels?
    fn n_levels(&self) -> usize;
}

pub use {
    self::cell::Ref,
    self::stack::Stack,
    self::hashmap::HashMap,
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

impl Backtrackable for Dummy {
    fn push_level(&mut self) { self.n_levels += 1 }
    fn pop_levels(&mut self, n: usize) {
        debug_assert!(self.n_levels >= n);
        self.n_levels -= n;
    }
    fn n_levels(&self) -> usize { self.n_levels }
}
