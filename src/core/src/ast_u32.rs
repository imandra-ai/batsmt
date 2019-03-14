
//! AST defined as a `u32`.
//!
//! This AST is sufficient for any manager that will store terms in a `Vec`,
//! and allows us to define common types for Sets and Maps.

use {
    std::u32, crate::ast::{self, View, },
};

/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST(u32);

impl AST {
    /// A value of type AST. Only ever use to fill array, do not access.
    pub const SENTINEL : AST = AST(u32::MAX);

    /// Access the underlying integer.
    #[inline(always)]
    pub const fn idx(&self) -> u32 { self.0 }
}

impl ast::HasID for AST {
    fn get_id(&self) -> Option<usize> { Some(self.0 as usize) }
}

pub mod manager_util {
    use super::*;

    /// Create a new AST value.
    ///
    /// *NOTE*: this should only be used when implementing AST managers.
    #[inline(always)]
    pub fn ast_from_u32(x: u32) -> AST {
        assert_ne!(x, u32::MAX, "overflow in AST creation");
        ast_from_u32_unchecked(x)
    }

    pub const fn ast_from_u32_unchecked(x: u32) -> AST {
        AST(x)
    }
}

/// A hashmap whose keys are AST nodes
pub type HashMap<V> = ast::HashMap<AST, V>;

/// A hashset whose keys are AST nodes
pub type HashSet = ast::HashSet<AST>;

/// Compute size of the term, seen as a tree.
pub fn ast_size_tree<M:ManagerU32>(m: &mut M, t: &AST) -> usize {
    ast::map_dag(
        m, t,
        |_| (),
        |_m, _u, view:View<(),usize>| {
            match view {
                View::Const(()) | View::Index(..) => 1usize,
                View::App{f, args} => {
                    args.iter().fold(1 + f, |x,y| x+y) // 1+sum of sizes
                },
            }
        })
}

/// A refinement of `Manager` where AST is the u32 AST.
pub trait ManagerU32 : ast::Manager<AST=AST> {}

// auto impl
impl<M> ManagerU32 for M where M: ast::Manager<AST=AST> {}
