
//! Symbols
//!
//! This module defines logic symbols, i.e. any unique object that belongs
//! to the logic signature, set of sorts, custom domain elements
//! (such as arithmetic constants, datatype constructors, etc.)

use std::hash::{Hash,Hasher};
use std::any::Any;
use std::fmt::{self,Debug};

/// The unique identifier of a symbol
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct Symbol(u32);

pub enum View {
    Str {
        /// name of this symbol
        name: String,
    },
    Custom {
        content: Box<Custom>,
    }
}

/// Custom symbol, with dynamic typing
pub trait Custom : Any + Debug {
    /// equality for the given type.
    ///
    /// Typically, use `Any::downcast<Self>` on other other value to
    /// check if it's of the same type, and compare; otherwise return `false`
    fn eq(&self, &Any) -> bool;

    /// Hash the content
    fn hash(&self, &mut dyn Hasher);

    fn as_any(&self) -> &dyn Any where Self: Sized { &*self }
}

// hand-write this instance, as it goes to dynamic dispatch
impl Hash for Custom {
    fn hash<H:Hasher>(&self, h: &mut H) { self.hash(h) }
}

/* FIXME: is this doable?
impl PartialEq for Custom {
    fn eq(&self, other: &dyn Custom) -> bool {
        let a: &dyn Any = other.as_any();
        self.eq(&*other as &dyn Any)
    }
}
*/

impl Debug for View {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            View::Str {name} => write!(fmt, "{}", name),
            View::Custom {content} => content.fmt(fmt),
        }
    }
}

/// Manager for symbols.
pub struct SymbolManager {
    views: Vec<View>,
}

impl SymbolManager {
    /// Create a new symbol manager
    pub fn new() -> Self {
        // TODO: add "kind" builtin symbol
        SymbolManager {
            views: Vec::with_capacity(512),
        }
    }

    pub fn len(&self) -> usize { self.views.len() }

    /// Get the definition of the given symbol
    #[inline]
    pub fn view(&self, id: Symbol) -> &View {
        &self.views[id.0 as usize]
    }

    /// Make a named symbol.
    ///
    /// Note that calling this function twice with the same string
    /// will result in two distinct symbols (as if the second one
    /// was shadowing the first). Use an auxiliary hashtable if
    /// you want sharing.
    pub fn mk_str(&mut self, str: &str) -> Symbol {
        let view = View::Str{ name: str.to_string(), };
        let s = Symbol(self.views.len() as u32);
        self.views.push(view);
        s
    }
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_mk_str() {
        let mut m = SymbolManager::new();
        let s1 = m.mk_str("a");
        let s2 = m.mk_str("a");
        assert_ne!(s1, s2);
    }

}
