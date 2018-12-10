
//! Congruence closure

use {
    std::{
        ops::{Deref,DerefMut}, marker::PhantomData,
    },
    batsmt_core::{SharedRef,ast::{self,AST},Symbol},
};

/// The congruence closure
pub struct CC<S, M>
where S: Symbol,
      M : for<'a> SharedRef<'a, ast::Manager<S>>
{
    nodes: ast::DenseMap<Node>,
    m: M, // the AST manager
    m_s: PhantomData<S>,
}


impl<S, M> CC<S, M>
    where S: Symbol,
          M: for<'a> SharedRef<'a, ast::Manager<S>>
{
    /// Create a new congruence closure
    pub fn new(m: M) -> Self {
        CC {
            m, nodes: ast::DenseMap::new(node::SENTINEL),
            m_s: PhantomData::default(),
        }
    }

    pub fn m<'a>(&'a self) -> impl Deref<Target=ast::Manager<S>> + 'a { self.m.get() }
    pub fn m_mut<'a>(&'a self) -> impl DerefMut<Target=ast::Manager<S>> + 'a { self.m.get_mut() }
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

