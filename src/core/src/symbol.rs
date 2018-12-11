
use {
    std::{mem, fmt::{self,Debug}, slice},
};

/// View on a stored symbol
pub trait SymbolView<'a> {
    type View : 'a;

    /// Get a view of the raw pointer
    fn view(self) -> Self::View;
}

/// The interface for a representation of logic symbols.
///
/// Symbols should be any unique object that belongs
/// to the logic signature, set of sorts, custom domain elements
/// (such as arithmetic constants, datatype constructors, etc.).
///
/// The actual representation of a symbol is `Symbol::Owned`. It is hidden
/// behind a raw pointer (stored in unions, etc.) and accessed via the
/// custom reference that is a symbol.
pub trait Symbol : Copy + Sized + for<'b> SymbolView<'b> {
    type Owned; // owned version

    /// Cast the symbol into a (stable) pointer.
    unsafe fn to_ptr(s: Self::Owned) -> Self;

    /// Free resources, given a pointer
    unsafe fn free(self);
}

/// String symbols
pub mod str {
    use super::*;

    /// A basic implementation: just a string
    #[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd)]
    pub struct Sym {
        ptr: *const u8,
        len: usize,
        cap: usize,
    }

    impl Debug for Sym {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            let s: &str = self.view();
            s.fmt(out)
        }
    }

    impl<'a> SymbolView<'a> for Sym {
        type View = &'a str;

        /// View symbol as a string
        fn view(self) -> Self::View {
            use std::str;
            let Sym{ptr, len, ..} = self;
            let slice = unsafe{slice::from_raw_parts(ptr as *mut u8, len)};
            str::from_utf8(slice).unwrap()
        }
    }

    impl Sym {
        pub fn eq_str(&self, s: &str) -> bool {
            self.view() == s
        }
    }

    impl Symbol for Sym {
        type Owned = String;

        unsafe fn to_ptr(s: Self::Owned) -> Self {
            let sym = Sym{ptr: s.as_ptr(), len: s.len(), cap: s.capacity()};
            mem::forget(s);
            sym
        }

        unsafe fn free(self) {
            let Sym{ptr, len, cap} = self;
            let string = String::from_raw_parts(ptr as *mut u8, len, cap);
            drop(string)
        }
    }
}
