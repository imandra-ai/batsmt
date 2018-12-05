
//! Symbols
//!
//! This module defines logic symbols, i.e. any unique object that belongs
//! to the logic signature, set of sorts, custom domain elements
//! (such as arithmetic constants, datatype constructors, etc.)

use std::str::FromStr;
use std::hash::{Hash,Hasher};
use std::any::Any;
use std::fmt::{self,Debug};

/// A logic symbol
pub enum Symbol {
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

impl Debug for Symbol {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::Str {name} => write!(fmt, "{}", name),
            Symbol::Custom {content} => content.fmt(fmt),
        }
    }
}

impl Symbol {
    /// Make a symbol from the given string
    pub fn mk_str(s: String) -> Self { Symbol::Str {name:s} }

    pub fn eq_str(&self, s: &str) -> bool {
        match self {
            Symbol::Str{name} => s == name,
            _ => false,
        }
    }
}

pub enum Void {}

impl FromStr for Symbol {
    type Err = Void;
    fn from_str(s: &str) -> Result<Self,Self::Err> { Ok(Symbol::mk_str(s.to_string())) }
}
