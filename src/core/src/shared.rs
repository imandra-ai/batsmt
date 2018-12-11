
//! Shared resources

use {
    std::{
        ops::{Deref,DerefMut},
        cell::{self,RefCell},
        rc::Rc,
        sync::{RwLock,Arc,RwLockReadGuard,RwLockWriteGuard},
    }
};

/// A shared reference to some resource of type `T`
pub trait SharedRef<'a> : Sized + Clone {
    type Target;
    type Guard : 'a + Deref<Target=Self::Target>;
    type MutGuard : 'a + DerefMut<Target=Self::Target>;

    /// Access a read-only reference
    fn get(&'a self) -> Self::Guard;

    /// Access a non-aliased mutable reference
    fn get_mut(&'a self) -> Self::MutGuard;
}

impl<'a, T> SharedRef<'a> for Rc<RefCell<T>>
    where T: Sized+'a
{
    type Target = T;
    type Guard = cell::Ref<'a, T>;
    type MutGuard = cell::RefMut<'a, T>;
    fn get(&'a self) -> Self::Guard { self.borrow() }
    fn get_mut(&'a self) -> Self::MutGuard { self.borrow_mut() }
}

impl<'a, T> SharedRef<'a> for Arc<RwLock<T>>
    where T: Sized+'a
{
    type Target = T;
    type Guard = RwLockReadGuard<'a, T>;
    type MutGuard = RwLockWriteGuard<'a, T>;
    fn get(&'a self) -> Self::Guard { self.read().unwrap() }
    fn get_mut(&'a self) -> Self::MutGuard { self.write().unwrap() }
}




