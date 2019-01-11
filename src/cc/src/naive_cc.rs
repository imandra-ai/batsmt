
//! An as-simple-as-possible implementation of congruence closure.
//!
//! Little attention is given to the efficiency. We focus on simplicity here.

use {
    std::{
        collections::VecDeque, fmt,
    },
    fxhash::{FxHashMap,FxHashSet},
    batsmt_theory::Ctx,
    batsmt_pretty as pp,
    batsmt_core::{backtrack},
    crate::*,
};

enum Op<C:Ctx> {
    Merge(C::AST, C::AST, C::B),
}

/// A naive implementation of the congruence closure
pub struct NaiveCC<C:Ctx>{
    confl: Vec<C::B>,
    ops: backtrack::Stack<Op<C>>, // just keep the set of operations to do here
}

/// A class representative
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct Repr<AST>(AST);

// A non-incremental congruence closure.
//
// It returns highly-non-minimal conflicts, that basically involve all
// literals used so far.
struct Solve<'a, C:Ctx> {
    m: &'a C,
    confl: &'a mut Vec<C::B>,
    all_lits: FxHashSet<C::B>, // all literals used in ops so far
    root: FxHashMap<C::AST, Repr<C::AST>>, // term -> its root + expl
    //root: FxHashMap<AST, (Repr,Option<Expl<B>>)>, // term -> its root + expl
    parents: FxHashMap<Repr<C::AST>, SVec<C::AST>>, // term -> its direct superterms
    tasks: VecDeque<Task<C::AST>>, // tasks to perform
}

#[derive(Clone,Copy,Debug)]
enum Task<AST> {
    UpdateTerm(AST), // check for congruence
    Merge(AST,AST), // merge the two classes
}

impl<C:Ctx> CCInterface<C> for NaiveCC<C> {
    fn merge(&mut self, _m: &C, t1: C::AST, t2: C::AST, lit: C::B) {
        self.ops.push(Op::Merge(t1,t2,lit))
    }

    fn distinct(&mut self, _m: &C, _ts: &[C::AST], _lit: C::B) {
        unimplemented!("no handling of `distinct` in naiveCC")
    }

    fn final_check<A>(&mut self, m: &C, acts: &mut A)
        where A: Actions<C>
    {
        debug!("cc.check()");
        // create local solver
        self.confl.clear();
        let mut solve = Solve::new(m, &mut self.confl);
        // here is where we do all the work
        let ok = solve.check_internal(self.ops.as_slice());
        if !ok {
            let costly = true;
            acts.raise_conflict(&self.confl, costly);
        }
    }

    // NOTE: do not implement partial check at all.

    fn impl_descr() -> &'static str { "naive congruence closure"}

    fn explain_prop(&mut self, _m: &C, _p: C::B) -> &[C::B] {
        unreachable!() // never propagated anything
    }
}

impl<C:Ctx> NaiveCC<C> {
    /// Create a new congruence closure using the given `Manager`
    pub fn new() -> Self {
        NaiveCC {
            confl: vec!(),
            ops: backtrack::Stack::new(),
        }
    }
}

// just backtrack the set of operations we'll have to perform
impl<C:Ctx> backtrack::Backtrackable<C> for NaiveCC<C> {
    fn push_level(&mut self, _: &mut C) { self.ops.push_level() }
    fn n_levels(&self) -> usize { self.ops.n_levels() }
    fn pop_levels(&mut self, _: &mut C, n: usize) {
        self.ops.pop_levels(n, |_| ()) // we didn't do anything to cancel
    }
}

// main algorithm
impl<'a, C:Ctx> Solve<'a, C> {
    fn new(m: &'a C, confl: &'a mut Vec<C::B>) -> Self {
        let mut s = Solve {
            m,
            confl,
            root: FxHashMap::default(),
            parents: FxHashMap::default(),
            all_lits: FxHashSet::default(),
            tasks: VecDeque::new(),
        };
        // be sure to add true and false
        s.add_term(m.get_bool_term(true));
        s.add_term(m.get_bool_term(false));
        debug_assert_ne!(m.get_bool_term(true), m.get_bool_term(false));
        s
    }

    /// entry point
    pub fn check_internal(&mut self, ops: &[Op<C>]) -> bool {
        trace!("naive-cc.check (ops: {:?})", ops);
        for op in ops.iter() {
            let ok = self.perform_op(op);
            if !ok {
                // build conflict (all literals used so far, negated)
                self.confl.clear();
                self.confl.extend(self.all_lits.iter().map(|&l| !l));
                return false;
            }
        }
        true
    }


    // perform one operation to change the CC
    fn perform_op(&mut self, op: &Op<C>) -> bool {
        match op {
            Op::Merge(a,b,lit) => {
                // add terms, then merge
                self.merge(*a,*b,*lit)
            }
        }
    }

    // Find representative of `a`
    fn find(&self, mut a: C::AST) -> Repr<C::AST> {
        loop {
            let n = self.root.get(&a).expect("term not present");

            if a == n.0 {
                return n.clone()
            } else {
                a = n.0 // recurse
            }
        }
    }

    fn merge(&mut self, a: C::AST, b: C::AST, lit: C::B) -> bool {
        self.add_term(a);
        self.add_term(b);

        let ra = self.find(a);
        let rb = self.find(b);

        if ra == rb {
            true
        } else {
            trace!("merge {:?} and {:?}", pp::pp1(self.m,&ra.0), pp::pp1(self.m,&rb.0));
            self.all_lits.insert(lit); // may be involved in conflict

            self.tasks.push_back(Task::Merge(a,b));
            self.fixpoint();
            let ok = ! self.is_eq(self.b.true_, self.b.false_);
            ok
        }
    }

    // are `a` and `b` equal?
    fn is_eq(&self, a: C::AST, b: C::AST) -> bool {
        self.find(a) == self.find(b)
    }

    fn is_root(&self, r: &Repr<C::AST>) -> bool {
        self.find(r.0) == *r
    }

    // add subterms recursively
    fn add_term(&mut self, t: C::AST) {
        if ! self.root.contains_key(&t) {
            trace!("add-term {:?}", pp::pp1(self.m,&t));
            self.root.insert(t.clone(), Repr(t.clone()));
            self.parents.insert(Repr(t.clone()), SVec::new());
            self.tasks.push_back(Task::UpdateTerm(t));

            // add arguments to CC, and add `t` to its arguments' parents lists
            match self.m.view(&t) {
                CCView::App(_, args) | CCView::Distinct(args) => {
                    for &u in args.iter() {
                        self.add_term(u);
                        self.parents.get_mut(&self.find(u)).unwrap().push(t);
                    }
                    self.update_term(t);
                },
                CCView::Eq(a,b) => {
                    for &u in [a,b].iter() {
                        self.add_term(u);
                        self.parents.get_mut(&self.find(u)).unwrap().push(t);
                    }
                },
                CCView::Bool(_) | CCView::Opaque(_) => (),
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
    fn n_parents(&self, r: &Repr<C::AST>) -> usize {
        self.parents.get(&r).unwrap().len()
    }

    // are t and u congruent?
    fn congruent(&self, t: C::AST, u: C::AST) -> bool {
        if t == u { return true }

        match (self.m.view(&t), self.m.view(&u)) {
            (CCView::App{f:f1, args:args1}, CCView::App{f:f2, args: args2}) => {
                args1.len() == args2.len() &&
                    f1 == f2 &&
                    args1.iter().zip(args2.iter())
                    .all(|(u1,u2)| self.is_eq(*u1,*u2))
            },
            (CCView::Eq(a1,b1), CCView::Eq(a2,b2)) => {
                (self.is_eq(a1, a2) && self.is_eq(b1, b2)) ||
                (self.is_eq(a1, b2) && self.is_eq(b1, a2))
            },
            _ => false,
        }
    }

    // merge these two distinct representatives
    fn merge_repr(&mut self, mut ra: Repr<C::AST>, mut rb: Repr<C::AST>) {
        assert_ne!(ra, rb);
        debug_assert!(self.is_root(&ra));
        debug_assert!(self.is_root(&rb));

        // ensure `ra` is the biggest
        if self.n_parents(&ra) < self.n_parents(&rb) {
            std::mem::swap(&mut ra, &mut rb);
        }

        trace!("task::merge-repr {:?} into {:?}", pp::pp1(self.m,&rb.0), pp::pp1(self.m,&ra.0));
        self.root.insert(rb.0, ra.clone()); // rb --> ra now

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

        for &t in parents_a.iter().chain(parents_b.iter()) {
            match self.m.view(&t) {
                CCView::Eq(a,b) if self.is_eq(a,b) => {
                    // `a=b` where a and b are merged --> merge with true
                    new_congr.push((t, self.m.get_bool_term(true)));
                },
                _ => ()
            }
        }

        // merge parents_b into parents_a and put it back into place
        {
            parents_a.extend_from_slice(&parents_b);
            self.parents.insert(ra, parents_a);
        }

        for (t,u) in new_congr {
            trace!("merge congruent parents: {:?} and {:?}", pp::pp1(self.m,&t), pp::pp1(self.m,&u));
            self.tasks.push_back(Task::Merge(t,u))
        }
    }

    fn push_congruence(&mut self, t: C::AST, u: C::AST) {
        trace!("update-term({:?}): merge with {:?}", pp::pp1(m,&t), pp::pp1(m,&u));
        self.tasks.push_back(Task::Merge(t,u))
    }

    fn update_term_with_args<I>(&mut self, t: C::AST, args: I)
        where I: Iterator<Item=C::AST>
    {
        let mut new_congr = SVec::new();

        // look in parents of `f` and `args` for congruent terms
        for &p in args {
            let rp = self.find(p);
            let parents_p = self.parents.get(&rp).unwrap();

            for &u in parents_p.iter() {
                if t != u && self.congruent(t, u) {
                    new_congr.push((t,u));
                }
            }
        }

        for (t,u) in new_congr {
            self.push_congruence(t,u)
        }
    }

    // this new term `t` might be congruent to other terms.
    //
    // Look for these based on t's arguments' parents
    fn update_term(&mut self, t: C::AST) {
        match self.m.view(&t) {
            CCView::Bool(_) | CCView::Opaque(_) => (),
            CCView::Apply(_, args) | CCView::Distinct(args) => {
                self.update_term_with_args(args.iter())
            },
            CCView::ApplyHO(f, args) => {
                let args = args.iter().chain(Some(f).iter());
                self.update_term_with_args(args)
            },
            CCView::Eq(a,b) => {
                if self.is_eq(a,b) {
                    // `a=b` where a and b are merged --> merge with true
                    let u = self.m.get_bool_term(true);
                    self.push_congruence(t, u)
                }
            }
        };
    }
}

impl<C:Ctx> fmt::Debug for Op<C> {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Merge(a,b,lit) => write!(out, "merge({:?},{:?},{:?})",a,b,lit),
        }
    }
}

impl<C:Ctx> Clone for Op<C> {
    fn clone(&self) -> Self {
        match self {
            Op::Merge(a,b,c) => Op::Merge(*a,*b,*c),
        }
    }
}

impl<C:Ctx> Clone for NaiveCC<C> {
    fn clone(&self) -> Self {
        let NaiveCC {b, confl, ops} = self;
        NaiveCC {
            b: b.clone(), confl: confl.clone(), ops: ops.clone()
        }
    }
}
