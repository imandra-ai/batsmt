
//! Some utils

use {
    std::{
        cell::{self,Cell,RefCell},
        ops::{Deref,DerefMut},
    },
};

/// A structure `T` with a refcount and interior mutability
pub struct Shared<T>(*mut SharedCell<T>);

// a wrapped `T`, with a refcount
struct SharedCell<T> {
    rc: Cell<u16>,
    cell: RefCell<T>,
}

/// A borrowed reference to the shared `T`.
///
/// It has a limited lifetime (`'a`) but `deref`s into `T`
pub struct SharedRef<'a, T>(cell::Ref<'a, T>);

/// A borrowed mutable reference to the shared `T`
///
/// It has a limited lifetime (`'a`) and cannot be aliased, but `deref_mut`s into `T`.
pub struct SharedRefMut<'a, T>(cell::RefMut<'a, T>);

impl<'a, T> Deref for SharedRef<'a, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &Self::Target { self.0.deref() }
}

impl<'a, T> Deref for SharedRefMut<'a, T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &Self::Target { self.0.deref() }
}

impl<'a, T> DerefMut for SharedRefMut<'a, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target { self.0.deref_mut() }
}

impl<T> Shared<T> {
    /// Allocate a new shared reference to the given value of type `T`
    pub fn new(x: T) -> Self {
        // allocate on heap
        let b = Box::new(SharedCell {
            rc: Cell::new(1),
            cell: RefCell::new(x),
        });
        Shared(Box::into_raw(b))
    }

    #[inline(always)]
    pub fn borrow(&self) -> SharedRef<T> {
        let rc : &RefCell<_> = unsafe{ &(*self.0).cell };
        let r = rc.borrow();
        SharedRef(r)
    }

    #[inline(always)]
    pub fn borrow_mut(&self) -> SharedRefMut<T> {
        // interior mutability, here we come!
        let rc : &RefCell<_> = unsafe { &(*self.0).cell };
        let r = rc.borrow_mut();
        SharedRefMut(r)
    }
}

impl<T> Clone for Shared<T> {
    // clone and increment refcount
    fn clone(&self) -> Self {
        let rc = unsafe { &mut (*self.0).rc };
        rc.set(rc.get() + 1);
        Shared(self.0)
    }
}

impl<T> Drop for Shared<T> {
    // clone and increment refcount
    fn drop(&mut self) {
        let dead = {
            let rc = unsafe { &mut (*self.0).rc };
            let n = rc.get();
            debug_assert!(n > 0);
            rc.set(n - 1);
            n-1 == 0
        };
        if dead {
            let b: Box<SharedCell<_>> = unsafe { Box::from_raw(self.0) };
            drop(b)
        }
    }
}
