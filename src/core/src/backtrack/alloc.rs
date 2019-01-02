
//! Backtrackable allocator.

use {
    std::{default::Default},
    super::{Ref, },
};

/// A backtrackable allocator.
///
/// This allocator doesn't have a `free` method. It provides slices and pointers
/// that remain valid until we backtrack.
pub struct Alloc<T:Clone> {
    slices: Vec<Slice<T>>, // slices
    offset: Ref<Offset>, // slice+offset in slice
    sentinel: T,
}

// size of a slice
const SLICE_SIZE : usize = 4_096;

/// Slice index + offset in slice.
#[derive(Clone)]
struct Offset {
    sl_i: usize,
    i: usize, // index in slice
}

struct Slice<T> {
    sl: Box<[T]>,
}

impl<T:Clone> Alloc<T> {
    /// New allocator.
    ///
    /// This allocator provides methods to allocate objects and arrays of
    /// type `T` with a stack discipline.
    pub fn new(sentinel: T) -> Self {
        Alloc{
            slices: vec!(),
            offset: Ref::new(Offset::new()),
            sentinel,
        }
    }

    /// Allocate one single object.
    ///
    /// The object reference will be invalidated upon backtracking.
    pub fn alloc(&mut self) -> *mut T {
        let off = &mut self.offset;

        if off.sl_i == self.slices.len() {
            // allocate new slice
            let sl = Slice::new(self.sentinel.clone(), SLICE_SIZE);
            self.slices.push(sl);
        }
        debug_assert!(off.sl_i < self.slices.len());

        // current slice
        let sl = &mut self.slices[off.sl_i];
        debug_assert!(off.i < sl.len());
        let ptr = &mut sl.sl[off.i] as *mut T;
        off.i += 1;

        if off.i == sl.len() {
            // slice is full
            off.sl_i += 1;
            off.i = 0;
        }

        ptr
    }

    #[inline(always)]
    pub fn n_levels(&self) -> usize {
        self.offset.n_levels()
    }

    #[inline]
    pub fn push_level(&mut self) {
        self.offset.push_level();
    }

    #[inline]
    pub fn pop_levels(&mut self, n: usize) {
        if n == 0 { return }
        self.offset.pop_levels(n);
    }
}

impl<T:Default+Clone> Default for Alloc<T> {
    /// New allocator with a default `T` as a sentinel.
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T:Clone> Slice<T> {
    fn new(sentinel: T, size: usize) -> Self {
        let mut vec = Vec::with_capacity(size);
        vec.resize(size, sentinel);
        let sl = vec.into_boxed_slice();
        Slice{sl}
    }

    #[inline(always)]
    fn len(&self) -> usize { self.sl.len() }
}

impl Offset {
    fn new() -> Self { Offset {sl_i: 0, i: 0} }
}
