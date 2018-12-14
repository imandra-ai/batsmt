
//! An as-simple-as-possible implementation of congruence closure.
//!
//! Little attention is given to the efficiency. We focus on simplicity here.

use {
    std::{
        marker::PhantomData,
    },
    fxhash::FxHashMap,
    batsmt_core::{AST,ast,Symbol,backtrack},
    crate::{*,types::BLit},
};

#[derive(Clone,Copy,Debug)]
enum Op {
    Merge(AST,AST,BLit),
}

/// A naive implementation of the congruence closure
pub struct NaiveCC<S:Symbol>{
    m: ast::Manager<S>, // the AST manager
    b: Builtins, // builtin terms
    props: PropagationSet,
    confl: Vec<BLit>,
    ops: backtrack::Stack<Op>, // just keep the set of operations to do here
    m_s: PhantomData<S>,
}

/// A class representative
#[derive(Clone,Copy,Debug,Eq,PartialEq,Hash)]
struct Repr(AST);

// A non-incremental congruence closure
struct Solve<'a, S:Symbol> {
    m: ast::Manager<S>, // the AST manager
    b: Builtins, // builtin terms
    props: &'a mut PropagationSet,
    confl: &'a mut Vec<BLit>,
    ops: &'a [Op], // just keep the set of operations to do here
    m_s: PhantomData<S>,
    root: FxHashMap<AST, Repr>, // term -> its root
    parents: FxHashMap<AST, SVec<AST>>, // term -> its direct superterms
}


impl<S:Symbol> CCInterface for NaiveCC<S> {
    fn merge(&mut self, t1: AST, t2: AST, lit: BLit) {
        self.ops.push(Op::Merge(t1,t2,lit))
    }

    fn distinct(&mut self, _ts: &[AST], _lit: BLit) {
        unimplemented!("no handling of `distinct` in naiveCC")
    }

    fn check(&mut self) -> Result<&PropagationSet, Conflict> {
        info!("cc check!");
        let mut solve = Solve {
            m: self.m.clone(),
            b: self.b.clone(),
            props: &mut self.props,
            confl: &mut self.confl,
            ops: self.ops.as_slice(),
            m_s: self.m_s.clone(),
            root: FxHashMap::default(),
            parents: FxHashMap::default(),
        };
        // here is where we do all the work
        let ok = solve.check_internal();
        if ok {
            Ok(&self.props)
        } else {
            Err(Conflict(&self.confl))
        }
    }
}

mod cc {
    use super::*;

    impl<S:Symbol> NaiveCC<S> {
        /// Create a new congruence closure using the given `Manager`
        pub fn new(m: &ast::Manager<S>, b: Builtins) -> Self {
            NaiveCC {
                m: m.clone(), b,
                m_s: PhantomData::default(),
                props: PropagationSet::new(),
                confl: vec!(),
                ops: backtrack::Stack::new(),
            }
        }
    }

    impl<S:Symbol> backtrack::Backtrackable for NaiveCC<S> {
        fn push_level(&mut self) { self.ops.push_level() }
        fn n_levels(&self) -> usize { self.ops.n_levels() }
        fn pop_levels(&mut self, n: usize) {
            self.ops.pop_levels(n, |_| ()) // we didn't do anything to cancel
        }
    }

    // main algorithm
    impl<'a, S:Symbol> Solve<'a, S> {
        /// entry point
        pub(super) fn check_internal(&mut self) -> bool {

            panic!();

            true
        }

    }
}
