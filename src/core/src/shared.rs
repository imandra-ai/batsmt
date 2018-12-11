
//! Shared resources

use std::ops::{Deref,DerefMut};
use std::cell::{self,RefCell};
use std::sync::*;

/// A shared reference to some resource of type `T`
pub trait SharedRef<'a, T:Sized+'a> : Sized {
    type Guard : 'a + Deref<Target=T>;
    type MutGuard : 'a + DerefMut<Target=T>;

    fn get(&'a self) -> Self::Guard;
    fn get_mut(&'a self) -> Self::MutGuard;
}

impl<'a, T:Sized+'a> SharedRef<'a, T> for RefCell<T> {
    type Guard = cell::Ref<'a, T>;
    type MutGuard = cell::RefMut<'a, T>;
    fn get(&'a self) -> Self::Guard { self.borrow() }
    fn get_mut(&'a self) -> Self::MutGuard { self.borrow_mut() }
}

impl<'a, T:Sized+'a> SharedRef<'a, T> for RwLock<T> {
    type Guard = RwLockReadGuard<'a, T>;
    type MutGuard = RwLockWriteGuard<'a, T>;
    fn get(&'a self) -> Self::Guard { self.read().unwrap() }
    fn get_mut(&'a self) -> Self::MutGuard { self.write().unwrap() }
}




