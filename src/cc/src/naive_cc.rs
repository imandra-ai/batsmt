
//! An as-simple-as-possible implementation of congruence closure.
//!
//! Little attention is given to the efficiency. We focus on simplicity here.

use {
    std::{
        marker::PhantomData, collections::VecDeque, fmt,
    },
    fxhash::{FxHashMap,FxHashSet},
    batsmt_core::{AST,ast,ast::View,Symbol,backtrack},
    crate::{*,types::BoolLit},
};

type M<S> = ast::Manager<S>;

#[derive(Clone,Copy)]
enum Op<B> {
    Merge(AST,AST,B),
}

/// A naive implementation of the congruence closure
pub struct NaiveCC<S:Symbol,B>{
    m: ast::Manager<S>, // the AST manager
    b: Builtins, // builtin terms
    props: PropagationSet<B>,
    confl: Vec<B>,
    ops: backtrack::Stack<Op<B>>, // just keep the set of operations to do here
    m_s: PhantomData<S>,
}

/// A class representative
#[derive(Clone,Copy,Debug,Eq,PartialEq,Hash)]
struct Repr(AST);

// A non-incremental congruence closure.
//
// It returns highly-non-minimal conflicts, that basically involve all
// literals used so far.
struct Solve<'a, S:Symbol, B> {
    _props: &'a mut PropagationSet<B>,
    confl: &'a mut Vec<B>,
    all_lits: FxHashSet<B>, // all literals used in ops so far
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

impl<S:Symbol,B:BoolLit> CCInterface<B> for NaiveCC<S,B> {
    fn merge(&mut self, t1: AST, t2: AST, lit: B) {
        self.ops.push(Op::Merge(t1,t2,lit))
    }

    fn distinct(&mut self, _ts: &[AST], _lit: B) {
        unimplemented!("no handling of `distinct` in naiveCC")
    }

    fn final_check(&mut self) -> Result<&PropagationSet<B>, Conflict<B>> {
        debug!("cc.check()");
        // create local solver
        self.props.clear();
        self.confl.clear();
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

    // NOTE: do not implement partial check at all.

    fn impl_descr(&self) -> &'static str { "naive congruence closure"}
}

impl<S:Symbol,B:BoolLit> NaiveCC<S,B> {
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
impl<S:Symbol,B> backtrack::Backtrackable for NaiveCC<S,B> {
    fn push_level(&mut self) { self.ops.push_level() }
    fn n_levels(&self) -> usize { self.ops.n_levels() }
    fn pop_levels(&mut self, n: usize) {
        self.ops.pop_levels(n, |_| ()) // we didn't do anything to cancel
    }
}

// main algorithm
impl<'a, S:Symbol, B:BoolLit> Solve<'a, S, B> {
    fn new(m: &'a M<S>, b: Builtins,
           props: &'a mut PropagationSet<B>,
           confl: &'a mut Vec<B>) -> Self
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
    pub(super) fn check_internal(&mut self, ops: &[Op<B>]) -> bool {
        trace!("naive-cc.check (ops: {:?})", ops);
        for &op in ops.iter() {
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
    fn perform_op(&mut self, op: Op<B>) -> bool {
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

    fn merge(&mut self, a: AST, b: AST, lit: B) -> bool {
        self.add_term(a);
        self.add_term(b);

        let ra = self.find(a);
        let rb = self.find(b);

        if ra == rb {
            true
        } else {
            trace!("merge {:?} and {:?}", self.m.pp(ra.0), self.m.pp(rb.0));
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
            trace!("add-term {:?}", self.m.pp(t));
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

        trace!("task::merge-repr {:?} into {:?}", self.m.pp(rb.0), self.m.pp(ra.0));
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

        for &t in parents_a.iter().chain(parents_b.iter()) {
            match self.m.get().view(t) {
                View::App {f, args} => {
                    // `a=b` where a and b are merged --> merge with true
                    if f == self.b.eq && self.is_eq(args[0], args[1]) {
                        new_congr.push((t, self.b.true_));
                    }
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
            trace!("merge congruent parents: {:?} and {:?}", self.m.pp(t), self.m.pp(u));
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

                // `a=b` where a and b are merged --> merge with true
                if f == self.b.eq && self.is_eq(args[0], args[1]) {
                    new_congr.push((t, self.b.true_));
                }

                for (t,u) in new_congr {
                    trace!("update-term({:?}): merge with {:?}", m.pp(t), m.pp(u));
                    self.tasks.push_back(Task::Merge(t,u))
                }
            },
            _ => (),
        };
    }
}

impl<B:BoolLit> fmt::Debug for Op<B> {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Op::Merge(a,b,lit) => write!(out, "merge({:?},{:?},{:?})",a,b,lit),
        }
    }
}
