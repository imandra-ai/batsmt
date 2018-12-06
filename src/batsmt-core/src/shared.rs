
//! Shared resources

use std::ops::{Deref,DerefMut};
use std::cell::{self,RefCell};
use std::sync::{self,RwLock};

/// A shared reference to some resource of type `T`
pub trait SharedRef<'a, T:Sized+'a> : Sized {
    type Guard : 'a + Deref<Target=T>;
    type MutGuard : 'a + DerefMut<Target=T>;

    fn borrow(&'a self) -> Self::Guard;
    fn borrow_mut(&'a mut self) -> Self::MutGuard;
}

impl<'a, T:Sized+'a> SharedRef<'a, T> for RefCell<T> {
    type Guard = cell::Ref<'a, T>;
    type MutGuard = cell::RefMut<'a, T>;
    fn borrow(&'a self) -> Self::Guard { self.borrow() }
    fn borrow_mut(&'a mut self) -> Self::MutGuard { self.borrow_mut() }
}

impl<'a, T:Sized+'a> SharedRef<'a, T> for RwLock<T> {
    type Guard = sync::RwLockReadGuard<'a, T>;
    type MutGuard = sync::RwLockWriteGuard<'a, T>;
    fn borrow(&'a self) -> Self::Guard { self.borrow() }
    fn borrow_mut(&'a mut self) -> Self::MutGuard { self.borrow_mut() }
}




