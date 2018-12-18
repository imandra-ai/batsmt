
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

/// A backtrackable reference.
///
/// Its content must be clonable because a copy of it is saved
/// every time `push_level` is called.
#[derive(Clone)]
pub struct Ref<T:Clone> {
    cur: T,
    st: Vec<T>,
}

impl<T:Clone> Ref<T> {
    /// New reference, containing `x` initially.
    pub fn new(x:T) -> Self {
        Ref {cur: x, st: vec!(), }
    }

    /// Access the current content.
    pub fn get(&self) -> &T { &self.cur }

    /// Access mutably the current content.
    ///
    /// This will never modify the copies saved by calls to `push_level`.
    pub fn get_mut(&mut self) -> &mut T { &mut self.cur }

    /// Push a backtracking point.
    pub fn push_level(&mut self) { self.st.push(self.cur.clone()) }

    /// Remove `n` backtracking points.
    pub fn pop_levels(&mut self, n: usize) {
        if n > self.st.len() { panic!("cannot pop {} levels", n) }

        let idx = self.st.len() - n;
        std::mem::swap(&mut self.cur, &mut self.st[idx]); // restore
        self.st.resize(idx, self.cur.clone());
    }

    /// Number of levels.
    pub fn n_levels(&self) -> usize { self.st.len() }
}

impl<T:Clone> std::ops::Deref for Ref<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target { self.get() }
}

impl<T:Clone> std::ops::DerefMut for Ref<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { self.get_mut() }
}
