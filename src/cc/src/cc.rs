
//! Congruence closure

use {
    std::{
        //ops::{Deref,DerefMut},
        marker::PhantomData,
        fmt::{self,Debug},
        collections::VecDeque,
    },
    batsmt_core::{ast::{self,AST},Symbol,backtrack},
    batsat::{Lit as BLit},
    smallvec::SmallVec,
};

/// The congruence closure
pub struct CC<S> where S: Symbol {
    m: ast::Manager<S>, // the AST manager
    stack: backtrack::Stack<Op>,
    m_s: PhantomData<S>,
    cc0: CC0,
}

/// internal state of the congruence closure
struct CC0 {
    nodes: ast::DenseMap<Node>,
    expl: ast::DenseMap<(AST, Expl)>, // proof forest
    tasks: VecDeque<Op>, // operations to perform
}

/// One node in the congruence closure's E-graph
#[derive(Clone)]
pub(crate) struct Node {
    ast: AST,
    cls_next: AST,
    cls_prev: AST,
    root: Repr, // current representative
}

/// A representative
#[derive(Clone,Copy,Eq,PartialEq,Hash,Ord,PartialOrd)]
pub struct Repr(AST);

const N_EXPL_MERGE : usize = 3;

/// A set of merges
#[derive(Clone)]
struct Merges(SmallVec<[(Repr,Repr); N_EXPL_MERGE]>);

/// An explanation for a merge
#[derive(Debug,Clone)]
enum Expl {
    Lit(BLit),
    Merges(Merges),
}

// backtrackable operations on the congruence closure
enum Op {
    Merge(Repr, Repr, Expl),
}

mod cc {
    use super::*;

    impl CC0 {
        fn new() -> Self {
            CC0{
                nodes: ast::DenseMap::new(node::SENTINEL),
                expl: ast::DenseMap::new((AST::SENTINEL, expl::SENTINEL)),
                tasks: VecDeque::new(),
            }
        }
    }

    impl<S> CC<S> where S: Symbol {
        /// Create a new congruence closure
        pub fn new(m: ast::Manager<S>) -> Self {
            CC {
                m,
                m_s: PhantomData::default(),
                stack: backtrack::Stack::new(),
                cc0: CC0::new(),
            }
        }

        pub fn m(&self) -> &ast::Manager<S> { &self.m }
        pub fn m_mut(&mut self) -> &mut ast::Manager<S> { &mut self.m }
    }

    impl<S: Symbol> backtrack::Backtrackable for CC<S> {
        fn push_level(&mut self) {
            self.stack.promote(&mut self.cc0).push_level();
        }

        fn pop_levels(&mut self, n: usize) {
            self.stack.promote(&mut self.cc0).pop_levels(n)
        }

        fn n_levels(&self) -> usize { self.stack.n_levels() }
    }

    impl backtrack::PerformOp<Op> for CC0 {
        fn do_op(&mut self, op: &mut Op) {
            unimplemented!(); // TODO
        }

        fn undo_op(&mut self, op: &mut Op) {
            unimplemented!(); // TODO
        }
    }
}

mod node {
    use super::*;

    /// The default `node` object
    pub(super) const SENTINEL : Node = Node::new(AST::SENTINEL);

    impl Node {
        /// Create a new node
        pub const fn new(ast: AST) -> Self {
            Node {
                ast, cls_prev: ast, cls_next: ast,
                root: Repr(ast),
            }
        }

        /// Is this node a root?
        pub fn is_root(&self) -> bool { self.root.0 == self.ast }

        /// Representative of the class
        pub fn repr(&self) -> Repr { self.root }
    }
}

pub(crate) mod expl {
    use super::*;

    /// Sentinel explanation, do not use
    pub(super) const SENTINEL : Expl = Expl::Lit(BLit::UNDEF);
}

mod merges {
    use super::*;

    impl Debug for Merges {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "merges(")?;
            for (r1,r2) in self.0.iter() {
                write!(out, "(= {:?} {:?})", r1.0, r2.0)?;
            }
            write!(out, ")")
        }
    }
}

