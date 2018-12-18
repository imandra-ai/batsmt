
//! Refcounted strings

use {
    std::{
        mem, fmt, slice, str, ptr, u16, usize, cell::Cell,
        sync::atomic::{Ordering,AtomicUsize},
        alloc::{Layout, alloc, dealloc},
    },
};

/// refcount implementation
pub trait RC : Sized {
    fn new() -> Self where Self : Sized; // starts at one
    fn incr(&self);
    fn decr_and_check_if_zero(&self) -> bool; // return `true` if reached 0
}

impl RC for Cell<u16> {
    fn new() -> Self { Cell::new(1) }
    fn incr(&self) {
        let n = self.get();
        if n == u16::MAX { panic!("refcount overflow"); }
        self.set(n+1);
    }
    fn decr_and_check_if_zero(&self) -> bool {
        let n = self.get();
        if n == 0 { panic!("refcount underflow"); }
        self.set(n-1);
        n == 1
    }
}

impl RC for AtomicUsize {
    fn new() -> Self { AtomicUsize::new(1) }
    fn incr(&self) {
        let n = self.fetch_add(1, Ordering::Release);
        if n == usize::MAX { panic!("refcount overflow"); }
    }
    fn decr_and_check_if_zero(&self) -> bool {
        let n = self.fetch_sub(1, Ordering::Release);
        if n == 0 { panic!("refcount underflow"); }
        n == 1
    }
}

/// A refcounted heap allocated string.
pub struct RCString<R : RC = Cell<u16>>(*const RCStringCell<R>);

unsafe impl<R:RC+Sync> Sync for RCString<R> {}

unsafe impl<R:RC+Send> Send for RCString<R> {}

/// The internal string on the heap.
struct RCStringCell<R : RC> {
    rc: R,
    len: usize,
    s: [u8],
}

// compute size
fn size_for_len<R>(n: usize) -> usize {
    mem::size_of::<R>() + mem::size_of::<usize>() + mem::size_of::<u8>() * n
}

impl RCString<Cell<u16>> {
    /// Allocate a new string refcounted with u16
    pub fn new(s: &str) -> Self {
        let r = RC::new();
        unsafe { RCString::init(r, s) }
    }
}

impl RCString<AtomicUsize> {
    /// Allocate a new string refcounted with u16
    pub fn new_atomic(s: &str) -> Self {
        let r: AtomicUsize = RC::new();
        unsafe { RCString::init(r, s) }
    }
}

impl<R:RC> RCString<R> where R: Sized {
    /// Allocate a new refcounted string
    pub fn new_with(s: &str) -> Self {
        let r = R::new();
        unsafe { RCString::init(r, s) }
    }

    unsafe fn init(r: R, s: &str) -> Self {
        let u = s.as_bytes();
        let size = size_for_len::<R>(u.len());
        let layout = Layout::from_size_align(size, 8).expect("cannot construct layout for rcstr");
        let slice: &mut [u8] = slice::from_raw_parts_mut(alloc(layout), size);
        let ptr = mem::transmute::<&mut [u8], &mut RCStringCell<R>>(slice);
        ptr.rc = r;
        ptr.len = u.len();
        {
            let uptr = u.as_ptr();
            ptr::copy(uptr, ptr.s.as_ptr() as *mut u8, u.len());
        }
        RCString(ptr as *const _)
    }

    fn get(&self) -> &RCStringCell<R> {
        unsafe { & (*(self.0 as *const RCStringCell<_>)) }
    }

    fn get_mut(&self) -> &mut RCStringCell<R> {
        unsafe { &mut ( *(self.0 as *mut RCStringCell<_>)) }
    }

    fn as_str(&self) -> &str {
        let cell = self.get();
        let slice = unsafe { slice::from_raw_parts(&cell.s[0], cell.len) };
        unsafe { str::from_utf8_unchecked(slice) }
    }
}

impl<R:RC> Clone for RCString<R> {
    fn clone(&self) -> Self {
        let c = self.get_mut();
        c.rc.incr();
        RCString(self.0)
    }
}

impl<R:RC> Drop for RCString<R> {
    fn drop(&mut self) {
        let c = self.get_mut();
        if c.rc.decr_and_check_if_zero() {
            let len = c.len;
            let ptr: *mut u8 = self.0 as *mut u8;
            let size = size_for_len::<R>(len);
            let layout = Layout::from_size_align(size, 8).expect("cannot construct layout for rcstr");
            unsafe { dealloc(ptr, layout); }
        }
    }
}

impl<R:RC> std::ops::Deref for RCString<R> {
    type Target = str;
    fn deref(&self) -> &Self::Target { self.as_str() }
}

impl<R:RC> std::borrow::Borrow<str> for RCString<R> {
    fn borrow(&self) -> &str { self.as_str() }
}

impl<R:RC> fmt::Display for RCString<R> {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(out)
    }
}

impl<R:RC> fmt::Debug for RCString<R> {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(out)
    }
}

impl<R:RC> PartialEq<str> for RCString<R> {
    fn eq(&self, s: &str) -> bool { self.as_str() == s }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_rc() {
        let s = RCString::new("abc");
        assert_eq!(s.as_str(), "abc");

        {

            let s2 = s.clone();
            assert_eq!(&s2, "abc");

            let t = RCString::new("foo bar");
            assert_eq!(&t, "foo bar");

            let s3 = s.clone();
            assert_eq!(&s3, "abc");

            let t2 = t.clone();
            assert_eq!(&t2, "foo bar");

            drop(t2);

            assert_eq!(&t, "foo bar");

            drop(t)
        }

        drop(s)
    }

    #[test]
    fn test_rc_thread() {
        use std::thread::spawn;
        let s = RCString::new_atomic("hello world");

        let mut threads = vec!();

        for _i in 0 .. 10 {
            let s2 = s.clone();
            let t = spawn(move|| {
                let s3 = s2.clone();
                &s3 == "hello world"
            });
            threads.push(t)
        }

        drop(s);

        for t in threads {
            let b = t.join().unwrap();
            assert!(b, "must be true");
        }
    }
}

