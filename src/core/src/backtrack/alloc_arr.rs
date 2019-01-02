
//! Backtrackable allocator.

use {
    std::{u32, default::Default},
    super::{Ref, Stack as BStack},
};

/// A backtrackable allocator.
///
/// This allocator doesn't have a `free` method. It provides slices and pointers
/// that remain valid until we backtrack.
pub struct Alloc<T:Clone> {
    slices: Vec<Slice<T>>, // slices
    first_non_empty: Ref<usize>, // first non-empty slice.
    big_arrays: BStack<Array<T>>, // arrays that are allocated separately
    sentinel: T,
}

/// An array of objects that live inside the allocator.
///
/// This array should never outlive the `push_level()` it was created in.
pub struct Array<T> {
    ptr: *mut T,
    len: u32,
}

// max size of an array allocated inside a slice.
//
// MUST be smaller than SLICE_SIZE
const MAX_ARR_SIZE : usize = 64;

// size of a slice
const SLICE_SIZE : usize = 4_096;

/// The state of a slice.
#[derive(Copy,Clone,Eq,PartialEq)]
struct Offset {
    i: u32, // first free slot
    available: u32, // invariant: `SLICE_SIZE-offset`
}

struct Slice<T> {
    sl: Box<[T]>,
    offset: Ref<Offset>,
}

impl<T:Clone> Alloc<T> {
    /// New allocator.
    ///
    /// This allocator provides methods to allocate objects and arrays of
    /// type `T` with a stack discipline.
    pub fn new(sentinel: T) -> Self {
        Alloc{
            slices: vec!(),
            first_non_empty: Ref::new(0),
            big_arrays: BStack::new(),
            sentinel,
        }
    }

    /// Allocate one single object.
    ///
    /// The object reference will be invalidated upon backtracking.
    pub fn alloc(&mut self) -> *mut T {
        let sl_i = *self.first_non_empty;

        if sl_i == self.slices.len() {
            self.alloc_slice();
        }
        debug_assert!(sl_i < self.slices.len());

        // current slice
        let sl = &mut self.slices[sl_i];
        let ptr = sl.alloc();

        if sl.offset.available == 0 {
            self.update_first_non_empty(sl_i + 1);
        }

        ptr
    }

    /// Allocate an array.
    ///
    /// The array will be invalidated upon backtracking.
    pub fn alloc_arr(&mut self, n: usize) -> Array<T> {
        let sentinel = self.sentinel.clone();

        if n > MAX_ARR_SIZE as usize {
            // allocate separately
            let mut v = Vec::with_capacity(n);
            v.resize(n, sentinel);
            let arr = v.into_boxed_slice();
            self.big_arrays.push(unsafe { arr.unsafe_clone() });
            Array { ptr: arr.as_mut_ptr(), len: n }
        } else {
            // find a slice that can allocate this array.
            let sl_i_0 = *self.first_non_empty;
            let mut sl_i = sl_i_0;

            while sl_i < self.slices.len() {
                if self.slices[sl_i].can_alloc_arr(n) { break }
            }

            // found no slice? allocate one.
            if sl_i == self.slices.len() {
                self.alloc_slice();
            }
            debug_assert!(sl_i < self.slices.len());
            debug_assert!(self.slices[sl_i].can_alloc_arr(n));

            let arr = self.slices[sl_i].alloc_arr(n);

            if sl_i == sl_i_0 && self.slices[sl_i].is_full ()
                // maybe the first slice is full now
                self.update_first_non_empty(sl_i+1);
            }
        }
    }

    // update `first_non_empty` pointer, starting at `sl_i`.
    fn update_first_non_empty(&mut self, mut sl_i: usize) {
        while sl_i < self.slices.len() && self.slices[sl_i].offset.available == 0 {
            sl_i += 1;
        }
        *self.first_non_empty = sl_i
    }

    #[inline(always)]
    pub fn n_levels(&self) -> usize {
        let n = self.first_non_empty.n_levels();
        debug_assert!(self.slices.iter().all(|sl| sl.offset.n_levels() == n));
        n
    }

    #[inline]
    pub fn push_level(&mut self) {
        self.first_non_empty.push_level();
        for sl in self.slices.iter_mut() {
            sl.push_level()
        }
    }

    pub fn pop_levels(&mut self, n: usize) {
        if n == 0 { return }

        self.first_non_empty.pop_levels(n);
        for sl in self.slices.iter_mut() {
            sl.pop_levels(n)
        }
    }

    // allocate a new slice.
    fn alloc_slice(&mut self) {
        let sl = Slice::new(self.sentinel.clone(), SLICE_SIZE, self.n_levels());
        self.slices.push(sl);
    }
}

impl<T:Default+Clone> Default for Alloc<T> {
    /// New allocator with a default `T` as a sentinel.
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T:Clone> Drop for Alloc<T> {
    fn drop(&mut self) {
        for arr in self.big_arrays.drain() {
            // allocated separately on the heap
            let len = arr.len as usize;
            let v = unsafe { Vec::from_raw_parts(arr.ptr, len, len) };
            drop(v)
        }
    }
}

impl<T:Clone> Slice<T> {
    fn new(sentinel: T, size: usize, n_levels: usize) -> Self {
        let mut vec = Vec::with_capacity(size);
        vec.resize(size, sentinel);
        let sl = vec.into_boxed_slice();
        let mut offset = Ref::new(Offset::new(size));
        // push n (empty) levels onto `offset`, so that all slices
        // have the same number of levels.
        for _i in 0 .. n_levels {
            offset.push_level();
        }
        Slice { sl, offset }
    }

    /// Allocate a single element
    fn alloc(&mut self) -> *mut T {
        debug_assert!(! self.is_full());
        let mut off = *self.offset;
        let ptr = &mut self.sl[off.i as usize] as *mut T;
        off.i += 1;
        off.available -= 1;
        *self.offset = off;
        ptr
    }

    /// Does this slice have room enough for `n` elements?
    fn can_alloc_arr(&self, n: usize) -> bool {
        self.offset.available as usize >= n
    }

    /// Allocate an array of `n` elements.
    ///
    /// precondition: `n` is small enough
    ///
    /// ## Safety
    fn alloc_arr(&mut self, n: usize) -> Array<T> {
        debug_assert!(n < u32::MAX as usize);
        debug_assert!(self.can_alloc_arr(n));
        let n = n as u32;

        let mut off = *self.offset;
        let ptr = &mut self.sl[off.i as usize] as *mut T;
        off.i += n;
        off.available -= n;
        *self.offset = off;
        Array {ptr, len: n}
    }

    #[inline(always)]
    fn is_full(&self) -> bool {
        self.offset.available == 0
    }

    #[inline(always)]
    pub fn push_level(&mut self) { self.offset.push_level() }

    #[inline(always)]
    pub fn pop_levels(&mut self, n: usize) { self.offset.pop_levels(n) }
}

impl Offset {
    fn new(size: usize) -> Self {
        Offset { i: 0, available: size as u32, }
    }
}

impl<T> Array<T> {
    /// Length of the array.
    #[inline(always)]
    pub fn len(&self) -> usize { self.len as usize }

    /// Access the `i`-th element.
    #[inline(always)]
    pub fn get(&self, i: usize) -> &T {
        if i >= self.len as usize { panic!("array.get") }

        let ptr = self.ptr.add(i);
        unsafe { &* ptr }
    }

    /// Access the `i`-th element, mutably.
    #[inline(always)]
    pub fn get_mut(&mut self, i: usize) -> &mut T {
        if i >= self.len as usize { panic!("array.get") }

        let ptr = self.ptr.add(i);
        unsafe { &mut * ptr }
    }

    // internal clone, only useful for big arrays. This introduces aliasing,
    // so it should be used with caution.
    unsafe fn unsafe_clone(&self) -> Self {
        Array { ptr: self.ptr, len: self.len }
    }
}

impl<T> std::ops::Index<usize> for Array<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, i: usize) -> &Self::Output { self.get(i) }
}

impl<T> std::ops::IndexMut<usize> for Array<T> {
    #[inline(always)]
    fn index_mut(&mut self, i: usize) -> &mut Self::Output { self.get_mut(i) }
}

#[cfg(test)]
mod test{
    use super::*;
    fn test_size() {
        assert!(MAX_ARR_SIZE <= SLICE_SIZE);
        assert!(SLICE_SIZE <= u32::MAX as usize);
    }
}
