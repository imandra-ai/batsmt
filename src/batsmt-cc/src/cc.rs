
//! Congruence closure

use {
    std::{
        ops::{Deref,DerefMut},
    },
    batsmt_core::{SharedRef,ast::{self,AST}},
};

/// The congruence closure
pub struct CC<M>
where M : for<'a> SharedRef<'a, ast::Manager>
{
    nodes: ast::DenseMap<Node>,
    m: M, // the AST manager
}


impl<M> CC<M>
    where M : for<'a> SharedRef<'a, ast::Manager>
{
    /// Create a new congruence closure
    pub fn new(m: M) -> Self {
        CC {
            m, nodes: ast::DenseMap::new(node::SENTINEL),
        }
    }

    pub fn m<'a>(&'a self) -> impl Deref<Target=ast::Manager> + 'a { self.m.get() }
    pub fn m_mut<'a>(&'a self) -> impl DerefMut<Target=ast::Manager> + 'a { self.m.get_mut() }
}

mod cc {
    use super::*;
}

/// One node in the congruence closure's E-graph
#[derive(Clone)]
pub(crate) struct Node {
    ast: AST,
}

mod node {
    use super::*;

    pub(crate) const SENTINEL : Node = Node { ast: AST::SENTINEL, };

    impl Node {

    }
}

