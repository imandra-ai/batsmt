
//! An as-simple-as-possible implementation of congruence closure.
//!
//! Little attention is given to the efficiency. We focus on simplicity here.

use {
    std::{
        marker::PhantomData, collections::VecDeque,
    },
    fxhash::{FxHashMap,FxHashSet},
    batsmt_core::{AST,ast,ast::View,Symbol,backtrack},
    crate::{*,types::BLit},
};

type M<S> = ast::Manager<S>;

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

// A non-incremental congruence closure.
//
// It returns highly-non-minimal conflicts, that basically involve all
// literals used so far.
struct Solve<'a, S:Symbol> {
    _props: &'a mut PropagationSet,
    confl: &'a mut Vec<BLit>,
    all_lits: FxHashSet<BLit>, // all literals used in ops so far
    m_s: PhantomData<S>,
    m: ast::Manager<S>, // the AST manager
    b: Builtins, // builtin terms
    root: FxHashMap<AST, Repr>, // term -> its root
    parents: FxHashMap<Repr, SVec<AST>>, // term -> its direct superterms
    tasks: VecDeque<Task>, // tasks to perform
}

#[derive(Clone,Copy,Debug)]
enum Task {
    UpdateTerm(AST), // check for congruence
    Merge(AST,AST), // merge the two classes
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
        // create local solver
        let mut solve =
            Solve::new(&self.m, self.b.clone(),
                &mut self.props,
                &mut self.confl);
        // here is where we do all the work
        let ok = solve.check_internal(self.ops.as_slice());
        if ok {
            Ok(&self.props)
        } else {
            Err(Conflict(&self.confl))
        }
    }
}

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

// just backtrack the set of operations we'll have to perform
impl<S:Symbol> backtrack::Backtrackable for NaiveCC<S> {
    fn push_level(&mut self) { self.ops.push_level() }
    fn n_levels(&self) -> usize { self.ops.n_levels() }
    fn pop_levels(&mut self, n: usize) {
        self.ops.pop_levels(n, |_| ()) // we didn't do anything to cancel
    }
}

// main algorithm
impl<'a, S:Symbol> Solve<'a, S> {
    fn new(m: &'a M<S>, b: Builtins,
           props: &'a mut PropagationSet,
           confl: &'a mut Vec<BLit>) -> Self
    {
        let mut s = Solve {
            m: m.clone(), b: b.clone(),
            _props: props,
            confl,
            m_s: PhantomData::default(),
            root: FxHashMap::default(),
            parents: FxHashMap::default(),
            all_lits: FxHashSet::default(),
            tasks: VecDeque::new(),
        };
        // be sure to add true and false
        s.add_term(b.true_);
        s.add_term(b.false_);
        s
    }

    /// entry point
    pub(super) fn check_internal(&mut self, ops: &[Op]) -> bool {
        for &op in ops.iter() {
            let ok = self.perform_op(op);
            if !ok {
                // copy conflict
                self.confl.extend(self.all_lits.iter());
                return false;
            }
        }
        true
    }


    // perform one operation to change the CC
    fn perform_op(&mut self, op: Op) -> bool {
        match op {
            Op::Merge(a,b,lit) => {
                // add terms, then merge
                self.merge(a,b,lit)
            }
        }
    }

    // Find representative of `a`
    fn find(&self, mut a: AST) -> Repr {
        loop {
            let n = self.root.get(&a).expect("term not present");

            if a == n.0 {
                return *n
            } else {
                a = n.0 // recurse
            }
        }
    }

    fn merge(&mut self, a: AST, b: AST, lit: BLit) -> bool {
        self.add_term(a);
        self.add_term(b);

        let ra = self.find(a);
        let rb = self.find(b);

        if ra == rb {
            true
        } else {
            trace!("merge {} and {}", self.m.display(ra.0), self.m.display(rb.0));
            self.all_lits.insert(lit); // may be involved in conflict

            self.tasks.push_back(Task::Merge(a,b));
            self.fixpoint();
            let ok = ! self.is_eq(self.b.true_, self.b.false_);
            ok
        }
    }

    // are `a` and `b` equal?
    fn is_eq(&self, a: AST, b: AST) -> bool {
        self.find(a) == self.find(b)
    }

    fn is_root(&self, r: Repr) -> bool {
        self.find(r.0) == r
    }

    // add subterms recursively
    fn add_term(&mut self, t: AST) {
        if ! self.root.contains_key(&t) {
            trace!("add-term {:?}", self.m.dbg_ast(t));
            self.root.insert(t, Repr(t));
            self.parents.insert(Repr(t), SVec::new());
            self.tasks.push_back(Task::UpdateTerm(t));

            // add arguments to CC, and add `t` to its arguments' parents lists
            let m = self.m.clone(); // multiple borrows
            match m.get().view(t) {
                View::App {f, args} => {
                    {
                        self.add_term(f);
                        self.parents.get_mut(&self.find(f)).unwrap().push(t);
                    }
                    for &u in args.iter() {
                        self.add_term(u);
                        self.parents.get_mut(&self.find(u)).unwrap().push(t);
                    }
                },
                View::Const(_) => (),
            };
        }
    }

    // perform tasks until none remains
    fn fixpoint(&mut self) {
        while let Some(t) = self.tasks.pop_front() {
            match t {
                Task::UpdateTerm(t) => {
                    self.update_term(t)
                },
                Task::Merge(a,b) => {
                    let ra = self.find(a);
                    let rb = self.find(b);

                    if ra != rb {
                        self.merge_repr(ra,rb)
                    }

                }

            }
        }
    }

    // number of parents of `r`
    fn n_parents(&self, r: Repr) -> usize {
        self.parents.get(&r).unwrap().len()
    }

    // are t and u congruent?
    fn congruent(&self, t: AST, u: AST) -> bool {
        if t == u { return true }

        let ok = match (self.m.get().view(t), self.m.get().view(u)) {
            (View::App{f:f1, args:args1}, View::App{f:f2, args: args2}) => {
                args1.len() == args2.len() &&
                    self.is_eq(f1,f2) &&
                    args1.iter().zip(args2.iter())
                    .all(|(u1,u2)| self.is_eq(*u1,*u2))
            },
            _ => false,
        };
        ok
    }

    // merge these two distinct representatives
    fn merge_repr(&mut self, mut ra: Repr, mut rb: Repr) {
        assert_ne!(ra, rb);
        debug_assert!(self.is_root(ra));
        debug_assert!(self.is_root(rb));

        // ensure `ra` is the biggest
        if self.n_parents(ra) < self.n_parents(rb) {
            std::mem::swap(&mut ra, &mut rb);
        }

        trace!("task::merge-repr {:?} into {:?}", self.m.dbg_ast(rb.0), self.m.dbg_ast(ra.0));
        self.root.insert(rb.0, ra); // rb --> ra now

        // move `parents_b` here
        let parents_b = self.parents.remove(&rb).unwrap();
        let mut parents_a = self.parents.remove(&ra).unwrap();

        // find merges between items of parents_a and parents_b
        let mut new_congr = SVec::new();
        for &t in parents_a.iter() {
            for &u in parents_b.iter() {
                if t != u && self.congruent(t, u) {
                    new_congr.push((t,u));
                }
            }
        }

        // merge parents_b into parents_a and put it back into place
        {
            parents_a.extend_from_slice(&parents_b);
            self.parents.insert(ra, parents_a);
        }

        for (t,u) in new_congr {
            trace!("merge congruent parents: {:?} and {:?}", self.m.dbg_ast(t), self.m.dbg_ast(u));
            self.tasks.push_back(Task::Merge(t,u))
        }
    }

    // this new term `t` might be congruent to other terms.
    //
    // Look for these based on t's arguments' parents
    fn update_term(&mut self, t: AST) {
        let m = self.m.clone();
        match m.get().view(t) {
            View::App {f, args} => {
                let mut new_congr = SVec::new();

                // look in parents of `f` and `args` for congruent terms
                for &p in args.iter().chain(Some(f).iter()) {
                    let rp = self.find(p);
                    let parents_p = self.parents.get(&rp).unwrap();

                    for &u in parents_p.iter() {
                        if t != u && self.congruent(t, u) {
                            new_congr.push((t,u));
                        }
                    }
                }

                for (t,u) in new_congr {
                    trace!("update-term({}): merge with {}", m.display(t), m.display(u));
                    self.tasks.push_back(Task::Merge(t,u))
                }
            },
            _ => (),
        };
    }
}
