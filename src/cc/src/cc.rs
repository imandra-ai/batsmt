
//! Congruence closure.
//!
//! The `CC` type is responsible for enforcing congruence and transitivity
//! of equality.

// TODO: signatures
// TODO: parametrize by "micro theories" (which just work on merges + expl)

use {
    std::{
        //ops::{Deref,DerefMut},
        cell::RefCell,
        marker::PhantomData,
        fmt::{self,Debug},
        collections::VecDeque,
    },
    batsmt_core::{ast::{self,AST},Symbol,backtrack},
    crate::{types::BLit,PropagationSet,Conflict,Builtins,CCInterface,SVec},
};

/// The congruence closure
pub struct CC<S> where S: Symbol {
    m: ast::Manager<S>, // the AST manager
    ok: bool, // no conflict?
    props: PropagationSet,
    confl: Vec<BLit>, // tmp for conflict
    stack: backtrack::Stack<UndoOp>,
    m_s: PhantomData<S>,
    cc0: RefCell<CC0>,
}

/// internal state of the congruence closure
struct CC0 {
    b: Builtins,
    nodes: ast::DenseMap<Node>,
    expl: ast::DenseMap<(AST, Expl)>, // proof forest
    tasks: VecDeque<Task>, // operations to perform
}

/// One node in the congruence closure's E-graph
#[derive(Debug,Clone)]
struct Node {
    id: NodeID,
    cls_next: NodeID,
    cls_prev: NodeID,
    root: Repr, // current representative (initially, itself)
}

/// The name for a node.
///
/// For now it's just the AST this node corresponds to.
#[derive(Debug,Clone,Copy,PartialEq,Eq,Hash,Ord,PartialOrd)]
struct NodeID(AST);

/// A representative
#[derive(Debug,Clone,Copy,Eq,PartialEq,Hash,Ord,PartialOrd)]
struct Repr(NodeID);

type Merge = (Repr,Repr);
type Merges = SVec<Merge>;

/// An explanation for a merge
#[derive(Clone)]
enum Expl {
    Lit(BLit),
    Merges(Merges), // congruence, injectivity, etc.
}

/// Undo operations on the congruence closure
enum UndoOp {
    Merge(Repr, Repr),
}

/// Operation to perform in the main fixpoint
enum Task {
    Merge(AST, AST, Expl),
    Distinct(SVec<AST>, Expl),
}

impl<S:Symbol> CCInterface for CC<S> {
    fn merge(&mut self, t1: AST, t2: AST, lit: BLit) {
        let expl = Expl::Lit(lit);
        self.cc0.borrow_mut().tasks.push_back(Task::Merge(t1,t2,expl))
    }

    fn distinct(&mut self, ts: &[AST], lit: BLit) {
        let mut v = SVec::with_capacity(ts.len());
        v.extend_from_slice(ts);
        let expl = Expl::Lit(lit);
        self.cc0.borrow_mut().tasks.push_back(Task::Distinct(v,expl))
    }

    fn check(&mut self) -> Result<&PropagationSet, Conflict> {
        info!("cc check!");
        self.check_internal()
    }
}

// main congruence closure operations
mod cc {
    use super::*;

    // main API
    impl<S> CC<S> where S: Symbol {
        /// Create a new congruence closure using the given `Manager`
        pub fn new(m: &ast::Manager<S>, b: Builtins) -> Self {
            CC {
                m: m.clone(),
                ok: true,
                m_s: PhantomData::default(),
                props: PropagationSet::new(),
                confl: vec!(),
                stack: backtrack::Stack::new(),
                cc0: RefCell::new(CC0::new(b)),
            }
        }

        #[inline(always)]
        pub fn m(&self) -> ast::ManagerRef<S> { self.m.get() }

        #[inline(always)]
        pub fn m_mut(&mut self) -> ast::ManagerRefMut<S> { self.m.get_mut() }
    }

    impl<S:Symbol> CC<S> {
        // main `check` function, performs the fixpoint
        pub(super) fn check_internal(&mut self) -> Result<&PropagationSet, Conflict> {
            let mut cc0 = self.cc0.borrow_mut();
            while let Some(task) = cc0.tasks.pop_front() {
                match task {
                    Task::Distinct(..) => unimplemented!("cannot handle distinct yet"),
                    Task::Merge(a,b,expl) => {
                        // TODO: find repr, if distinct then merge them
                        panic!()
                    },
                }
                panic!(); // TODO


            }
            Ok(&self.props)
        }

    }

    impl CC0 {
        /// Create a core congruence closure
        pub(super) fn new(b: Builtins) -> Self {
            CC0{
                nodes: ast::DenseMap::new(node::SENTINEL),
                expl: ast::DenseMap::new((AST::SENTINEL, expl::SENTINEL)),
                tasks: VecDeque::new(),
                b,
            }
        }

        /// Find representative of the given node
        fn find(&self, id: NodeID) -> Repr { self[id].root }

        fn perform_undo(&mut self, op: UndoOp) {
            match op {
                UndoOp::Merge(a,b) => {
                    if self[a.0].is_root() {
                        // unmerge b from a
                        let n = &mut self[b.0];
                        debug_assert!(! n.is_root());
                        n.root = b;
                    } else {
                        // unmerge a
                        debug_assert!(self[b.0].is_root());
                        let n = &mut self[a.0];
                        debug_assert!(! n.is_root());
                        n.root = a;
                    }
                }
            }
        }
    }

    impl std::ops::Index<NodeID> for CC0 {
        type Output = Node;
        #[inline(always)]
        fn index(&self, id: NodeID) -> &Self::Output {
            self.nodes.get(id.0).unwrap()
        }
    }

    impl std::ops::IndexMut<NodeID> for CC0 {
        #[inline(always)]
        fn index_mut(&mut self, id: NodeID) -> &mut Self::Output {
            self.nodes.get_mut(id.0).unwrap()
        }
    }

    impl<S: Symbol> backtrack::Backtrackable for CC<S> {
        fn push_level(&mut self) {
            let mut cc0 = self.cc0.borrow_mut();
            self.stack.push_level();
        }

        fn pop_levels(&mut self, n: usize) {
            let mut cc0 = self.cc0.borrow_mut();
            self.stack.pop_levels(n, |op| cc0.perform_undo(op))
        }

        fn n_levels(&self) -> usize { self.stack.n_levels() }
    }
}

// manipulating nodes
mod node {
    use super::*;

    pub(super) const UNDEF_ID : NodeID = NodeID(AST::SENTINEL);

    /// The default `node` object
    pub(super) const SENTINEL : Node = Node::new(UNDEF_ID);

    impl Eq for Node {}
    impl PartialEq for Node {
        fn eq(&self, other: &Node) -> bool { self.id == other.id }
    }

    impl From<AST> for NodeID {
        fn from(a: AST) -> Self { NodeID(a) }
    }

    impl Node {
        /// Create a new node
        pub const fn new(id: NodeID) -> Self {
            Node {
                id, cls_prev: id, cls_next: id,
                root: Repr(id),
            }
        }

        /// Is this node a root?
        pub fn is_root(&self) -> bool { self.root.0 == self.id }

        /// Representative of the class
        pub fn repr(&self) -> Repr { self.root }
    }
}

mod expl {
    use super::*;

    /// Sentinel explanation, do not use except for filling arrays
    pub(super) const SENTINEL : Expl = Expl::Lit(BLit::UNDEF);

    impl Expl {
        fn lit(x: BLit) -> Self { Expl::Lit(x) }
        fn merges(v: Merges) -> Self { Expl::Merges(v) }
    }

    impl Debug for Expl {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Expl::Lit(lit) => {
                    write!(out, "lit({:?})", lit)
                },
                Expl::Merges(vs) => {
                    write!(out, "merges(")?;
                    for (r1,r2) in vs.iter() {
                        write!(out, "(= {:?} {:?})", r1.0, r2.0)?;
                    }
                    write!(out, ")")
                }
            }
        }
    }
}

