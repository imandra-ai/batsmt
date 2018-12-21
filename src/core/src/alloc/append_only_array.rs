
//! Append-only array allocator.

use {
    std::{u32, default::Default},
};

/// Append-only array allocator.
///
/// This is intended to be used to allocate many small arrays, without `free`.
/// When the manager (eg `ast::Manager`) needs to free memory, it should do
/// it via GC, moving arrays to a new allocator and discarding the old one.
///
/// Maximum length of arrays is `u32::MAX`.
pub struct Alloc<T:Copy> {
    slices: Vec<Slice<T>>, // slices in which "small" arrays are allocated
    fill: T, // filling element
    p: Params,
    large: Vec<Box<[T]>>,
}

/// A managed array of elements of type `T`.
///
/// This array should *never* survive its allocator.
#[derive(Copy,Clone)]
pub struct Array<T:Copy> {
    len: u32,
    data: ArrayData<T>,
}

// Size for small-array optimization
const N_INLINE : u32 = 3;

#[derive(Copy,Clone)]
union ArrayData<T:Copy> {
    ptr: *mut T,
    array: [T; N_INLINE as usize],
}

/// Parameters for the allocator
#[derive(Copy,Clone,Debug)]
pub struct Params {
    pub slice_size: usize,
    pub max_array_size: u32, // maximum size of arrays allocated inline
}

// one slice
struct Slice<T> {
    ptr: Box<[T]>, // chunk of memory
    cur: usize, // offset of next available slot.
    available: usize, // invariant: `available = ptr[cur..].len()`
}

impl Default for Params {
    fn default() -> Self {
        Params {
            slice_size: 4_096,
            max_array_size: 32,
        }
    }
}

impl<T:Copy> std::ops::Deref for Array<T> {
    type Target = [T];
    #[inline(always)]
    fn deref(&self) -> &Self::Target { self.as_slice() }
}

impl Params {
    /// Are these parameters valid?
    pub fn validate(&self) -> bool {
        self.slice_size > 16 &&
            self.max_array_size >= 2 &&
            self.slice_size > self.max_array_size as usize
    }
}

impl<T:Copy+Default> Alloc<T> {
    /// New allocator, with default elements to fill it.
    pub fn new() -> Self {
        Self::new_with(Default::default())
    }
}

// Allocate a new array on the heap
fn alloc_slice_ptr<T:Copy>(len: usize, fill: T) -> Box<[T]> {
    let mut v = Vec::with_capacity(len);
    v.resize(len, fill);
    let b = v.into_boxed_slice();
    b
}

impl<T:Copy> Array<T> {
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        let len = self.len as usize;
        if self.len < N_INLINE {
            unsafe { & self.data.array[..len] }
        } else {
            unsafe { std::slice::from_raw_parts(self.data.ptr, len) }
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len as usize
    }
}

impl<T:Copy> Alloc<T> {
    /// New allocator, filled with the given element.
    pub fn new_with(x: T) -> Self {
        Alloc {
            p: Default::default(),
            fill: x,
            slices: vec!(),
            large: vec!(),
        }
    }

    /// Set parameters.
    ///
    /// Note that this will only affect future allocations.
    pub fn set_params(&mut self, p: Params) {
        if !p.validate() {
            panic!("cannot use invalid parameters {:?}", p)
        }
        self.p = p
    }

    /// Access parameters.
    pub fn get_params(&self) -> Params { self.p }

    fn alloc_(&mut self, n: usize) -> *mut T {
        if n > u32::MAX as usize { // TODO: annotate as "cold"
            panic!("cannot allocate array of size {}", n);
        }

        debug_assert!(n > N_INLINE as usize);

        if n as u32  > self.p.max_array_size {
            // allocate a fresh array with malloc
            let mut array = alloc_slice_ptr(n, self.fill);
            let r = array.as_mut_ptr(); // won't move
            self.large.push(array);
            r
        } else {
            let mut i = 0;

            // look for an available slice
            while i < self.slices.len() {
                let slice = &mut self.slices[i];
                if slice.remaining_size() >= n {
                    // use this slice
                    let ptr = {
                        let sl = &mut slice.ptr[slice.cur .. slice.cur + n];
                        sl.as_mut_ptr()
                    };
                    slice.cur += n;
                    slice.available -= n;
                    return ptr
                } else {
                    i += 1 // next!
                }
            }

            // didn't find room, allocate new slice
            {
                let cap = self.p.slice_size;
                debug_assert!(n < cap); // see: Params::validate
                let mut array = alloc_slice_ptr(cap, self.fill);
                let ptr = {
                    let sl = &mut array[0 .. n];
                    sl.as_mut_ptr()
                };
                let slice = Slice{ ptr: array, cur: n, available: cap-n};
                self.slices.push(slice);
                ptr
            }
        }
    }

    /// Allocate an array using the given allocator.
    ///
    /// ## Panics
    /// - if `n > u32::MAX`.
    pub fn alloc_from_slice(&mut self, a: &[T]) -> Array<T> {
        let len = a.len();
        let ptr = self.alloc_(len);

        if len < N_INLINE as usize {
            // allocate in local array
            let mut array = [self.fill; N_INLINE as usize];
            array[..a.len()].copy_from_slice(&a); // copy
            Array {len: len as u32, data: ArrayData{array}, }
        } else {
            let r = unsafe { std::slice::from_raw_parts_mut(ptr, len) };
            r.copy_from_slice(a); // copy data
            Array {len: len as u32, data: ArrayData{ptr}, }
        }
    }

    /// Allocate an array using the given allocator.
    ///
    /// Uses `f` to fill the elements.
    ///
    /// ## Panics
    /// - if `n > u32::MAX`.
    pub fn alloc_with<F>(&mut self, len: u32, mut f: F) -> Array<T>
        where F: FnMut(usize) -> T,
    {
        let len = len as usize;

        if len < N_INLINE as usize {
            // allocate in local array
            let mut array = [self.fill; N_INLINE as usize];
            for i in 0 .. len {
                array[i] = f(i); // fill
            }
            Array {len: len as u32, data: ArrayData{array}, }
        } else {
            // allocate on heap
            let ptr = self.alloc_(len);
            let r = unsafe { std::slice::from_raw_parts_mut(ptr, len) };
            for i in 0 .. len {
                r[i] = f(i); // fill
            }
            Array {len: len as u32, data: ArrayData{ptr}, }
        }
    }
}

impl<T> Slice<T> {
    /// Size of slice available for allocating new arrays.
    #[inline(always)]
    fn remaining_size(&self) -> usize {
        self.available
    }
}
