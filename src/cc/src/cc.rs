
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
    batsmt_core::{ast::{self,AST},Symbol,backtrack,theory},
    smallvec::SmallVec,
};

/// Boolean literal
pub type BLit = theory::BLit;

/// The congruence closure
pub struct CC<S> where S: Symbol {
    m: ast::Manager<S>, // the AST manager
    stack: backtrack::Stack<Op>,
    m_s: PhantomData<S>,
    cc0: RefCell<CC0>,
}

/// internal state of the congruence closure
struct CC0 {
    nodes: ast::DenseMap<Node>,
    expl: ast::DenseMap<(AST, Expl)>, // proof forest
    tasks: VecDeque<Task>, // operations to perform
}

/// One node in the congruence closure's E-graph
#[derive(Clone)]
struct Node {
    ast: AST,
    cls_next: AST,
    cls_prev: AST,
    root: Repr, // current representative
}

/// A representative
#[derive(Clone,Copy,Eq,PartialEq,Hash,Ord,PartialOrd)]
pub struct Repr(AST);

/// a small vector of `T`
pub type SVec<T> = SmallVec<[T; 3]>;

type Merge = (Repr,Repr);
type Merges = SVec<Merge>;

/// An explanation for a merge
#[derive(Clone)]
enum Expl {
    Lit(BLit),
    Merges(Merges),
}

/// Propagation: `guard => concl`
///
/// Note that `guard` literals should all be true in current trail.
pub struct Propagation {
    pub concl: BLit,
    pub guard: Vec<BLit>,
}

/// A conflict is a set of literals that forms a clause
pub struct Conflict(pub SVec<BLit>);

/// Backtrackable operations on the congruence closure
enum Op {
    Merge(Repr, Repr, Expl),
}

/// Operation to perform in the main fixpoint
enum Task {
    Merge(AST, AST, Expl),
    Distinct(SVec<AST>, Expl),
}

// main congruence closure operations
mod cc {
    use super::*;

    // main API
    impl<S> CC<S> where S: Symbol {
        /// Create a new congruence closure using the given `Manager`
        pub fn new(m: &ast::Manager<S>) -> Self {
            CC {
                m: m.clone(),
                m_s: PhantomData::default(),
                stack: backtrack::Stack::new(),
                cc0: RefCell::new(CC0::new()),
            }
        }

        #[inline(always)]
        pub fn m(&self) -> ast::ManagerRef<S> { self.m.get() }

        #[inline(always)]
        pub fn m_mut(&mut self) -> ast::ManagerRefMut<S> { self.m.get_mut() }

        /// `cc.merge(t1,t2,lit)` merges `t1` and `t2` with explanation `lit`.
        pub fn merge(&self, t1: AST, t2: AST, lit: BLit) {
            let expl = Expl::Lit(lit);
            self.cc0.borrow_mut().tasks.push_back(Task::Merge(t1,t2,expl))
        }

        /// `cc.distinct(terms,lit)` asserts that all elements of `terms` are disjoint
        pub fn distinct(&self, ts: &[AST], lit: BLit) {
            let mut v = SVec::with_capacity(ts.len());
            v.extend_from_slice(ts);
            let expl = Expl::Lit(lit);
            self.cc0.borrow_mut().tasks.push_back(Task::Distinct(v,expl))
        }

        /// Check if the set of `merge` and `distinct` seen so far is consistent.
        ///
        /// Returns `Ok(props)` if the result is safisfiable with propagations `props`,
        /// and `Err(c)` if `c` is a valid conflict clause that contradicts
        /// the current trail.
        pub fn check(&self) -> Result<SVec<Propagation>, Conflict> {
            info!("cc check!");
            unimplemented!() // TODO: fixpoint
        }
    }

    impl CC0 {
        fn new() -> Self {
            CC0{
                nodes: ast::DenseMap::new(node::SENTINEL),
                expl: ast::DenseMap::new((AST::SENTINEL, expl::SENTINEL)),
                tasks: VecDeque::new(),
            }
        }
    }

    impl<S: Symbol> backtrack::Backtrackable for CC<S> {
        fn push_level(&mut self) {
            let mut cc0 = self.cc0.borrow_mut();
            self.stack.promote(&mut *cc0).push_level();
        }

        fn pop_levels(&mut self, n: usize) {
            let mut cc0 = self.cc0.borrow_mut();
            self.stack.promote(&mut *cc0).pop_levels(n);
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

// manipulating nodes
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

