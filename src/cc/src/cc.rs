
//! Congruence closure.
//!
//! The `CC` type is responsible for enforcing congruence and transitivity
//! of equality.

// TODO: parametrize by "micro theories" (which just work on merges + expl)

// micro theories:
// - rule for `not` (t == true |- not t == false, and conversely)
// - rule for `ite` (t == true |- not t == false, and conversely)

use {
    std::{ u32, collections::VecDeque, hash::Hash, fmt::Debug, },
    batsmt_core::{ast::{self,Manager,AstMap,View},backtrack},
    batsmt_pretty as pp,
    crate::{
        types::{Ctx as ThCtx},
        PropagationSet,Conflict,Builtins,CCInterface,SVec,
    },
};

/// Public interface
pub trait Ctx: ThCtx + Sized {
    type Map : AstMap<Self::AST, Node<Self>> + Sized;

    fn new_map(sentinel: Node<Self>) -> Self::Map;
}

// auto impl
impl<C> Ctx for C
    where C: ThCtx, C::M : ast::WithDenseMap<C::AST, Node<C>>
{
    type Map = <C::M as ast::WithDenseMap<C::AST, Node<C>>>::DenseMap;
    fn new_map(sentinel: Node<C>) -> Self::Map {
        <C::M as ast::WithDenseMap<C::AST, Node<C>>>::new_dense_map()
    }
}

/// The congruence closure.
pub struct CC<C:Ctx> {
    b: Builtins<C::AST>,
    tasks: VecDeque<Task<C>>, // operations to perform
    undo: backtrack::Stack<UndoOp<C::AST>>,
    confl: Vec<C::B>, // local for conflict
    props: PropagationSet<C::B>, // local for propagations
    traverse: ast::iter_suffix::State<C::M, ast::AstHashSet<C::M>>, // for recursive traversal
    expl_st: Vec<Expl<C>>, // to expand explanations
    tmp_sig: Signature<C::AST>, // for computing signatures
    sig_tbl: backtrack::HashMap<Signature<C::AST>, C::AST>,
    cc1: CC1<C>,
}

/// internal state, with just the core structure for nodes and parent sets
struct CC1<C:Ctx> {
    ok: bool, // no conflict?
    nodes: Nodes<C::Map>,
}

/// Map terms into the corresponding node.
struct Nodes<Map>(Map);

/// One node in the congruence closure's E-graph.
///
/// It contains:
/// - the term itself
/// - a direct pointer to the class' root
/// - double-linked list pointers for iterating the class, along with the class' size
/// - the proof forest pointer
/// - an optional mapping from the term to a boolean literal (for propagation)
#[derive(Clone,Eq)]
struct Node<C:Ctx> where C::AST : Sized, C::B : Sized {
    id: C::AST,
    next: C::AST, // next elt in class
    size: u32, // number of elements in class
    expl: Option<(C::AST, Expl<C>)>, // proof forest
    as_lit: Option<C::B>, // if this term corresponds to a boolean literal
    root: Repr<C::AST>, // current representative (initially, itself)
    parents: ParentList<C::AST>, // parents of the given term
}

#[derive(Clone)]
struct ParentList<AST>(SVec<AST>);

/// A representative
#[derive(Debug,Clone,Copy,Eq,PartialEq,Hash,Ord,PartialOrd)]
struct Repr<AST>(AST);

/// An explanation for a merge
#[derive(Clone,Debug)]
enum Expl<C:Ctx> {
    Lit(C::B), // because literal was asserted
    Congruence(C::AST, C::AST), // because terms are congruent
    AreEq(C::AST, C::AST), // because terms are equal
}

/// Undo operations on the congruence closure
#[derive(Debug)]
enum UndoOp<AST> {
    SetOk,
    RemoveTerm(AST),
    UnmapLit(AST),
    Unmerge {
        root: Repr<AST>, // the new repr
        old_root: Repr<AST>, // merged into `a`
    }, // unmerge these two reprs
    RemoveExplLink(AST,AST), // remove explanation link connecting these
}

/// Operation to perform in the main fixpoint
#[derive(Debug)]
enum Task<C:Ctx> {
    AddTerm(C::AST), // add term if not present
    MapToLit(C::AST,C::B), // map term to lit
    UpdateSig(C::AST), // re-check signature
    Merge(C::AST, C::AST, Expl<C>), // merge the classes of these two terms
    Distinct(SVec<C::AST>, Expl<C>),
}

/// A signature for a term, obtained by replacing its subterms with their repr.
///
/// Signatures have the properties that if two terms are congruent,
/// then their signatures are identical.
#[derive(Eq,PartialEq,Hash,Clone,Debug)]
struct Signature<AST:Eq+Hash+Debug>(SVec<Repr<AST>>);

// implement main interface
impl<C:Ctx> CCInterface<C> for CC<C> {
    fn merge(&mut self, _m: &C::M, t1: C::AST, t2: C::AST, lit: C::B) {
        let expl = Expl::Lit(lit);
        self.tasks.push_back(Task::AddTerm(t1));
        self.tasks.push_back(Task::AddTerm(t2));
        self.tasks.push_back(Task::Merge(t1,t2,expl))
    }

    fn distinct(&mut self, _m: &C::M, ts: &[C::AST], lit: C::B) {
        let mut v = SVec::with_capacity(ts.len());
        v.extend_from_slice(ts);
        let expl = Expl::Lit(lit);
        self.tasks.push_back(Task::Distinct(v,expl))
    }

    fn add_literal(&mut self, _m: &C::M, t: C::AST, lit: C::B) {
        self.tasks.push_back(Task::AddTerm(t));
        self.tasks.push_back(Task::MapToLit(t, lit));
    }

    fn final_check(&mut self, m: &C::M) -> Result<&PropagationSet<C::B>, Conflict<C::B>> {
        debug!("cc.final-check()");
        self.check_internal(m)
    }

    fn partial_check(&mut self, m: &C::M) -> Result<&PropagationSet<C::B>, Conflict<C::B>> {
        debug!("cc.partial-check()");
        self.check_internal(m)
    }

    fn explain_propagation(&mut self, _m: &C::M, _p: C::B) -> &[C::B] {
        unimplemented!("explain propagation not implemented yet") // FIXME
    }

    // FIXME
    // fn has_partial_check() -> bool { true }
    fn has_partial_check() -> bool { false }

    fn impl_descr() -> &'static str { "fast congruence closure"}
}

impl<C:Ctx> CC<C> {
    // main `check` function, performs the fixpoint
    fn check_internal(&mut self) -> Result<&PropagationSet<C::B>, Conflict<C::B>> {
        debug!("check-internal ({} tasks)", self.tasks.len());
        self.run_tasks();
        if self.cc1.ok {
            Ok(&self.props)
        } else {
            debug_assert!(self.confl.len() >= 1); // must have some conflict
            Err(Conflict(&self.confl))
        }
    }

    /// Run tasks (add term, merges, etc.) until fixpoint.
    fn run_tasks(&mut self) {
        while let Some(task) = self.tasks.pop_front() {
            if ! self.cc1.ok {
                self.tasks.clear();
                break; // conflict detected, no need to continue
            }
            match task {
                Task::AddTerm(t) => self.add_term(t),
                Task::UpdateSig(t) => self.update_signature(t),
                Task::Merge(a,b,expl) => self.merge(a, b, expl),
                Task::MapToLit(t,lit) => self.map_to_lit(t, lit),
                Task::Distinct(..) => {
                    unimplemented!("cannot handle distinct yet")
                },
            }
        }
    }
}

/// Does `t` need to be entered in the signature table?
fn needs_signature<C:Ctx>(m: &C::M, t: C::AST) -> bool {
    match m.view(t) {
        View::Const(_) => false,
        View::App{..} => true,
    }
}

// main congruence closure operations
impl<C:Ctx> CC<C> {
    /// Create a new congruence closure.
    pub fn new(m: &C::M, b: Builtins<C::AST>) -> Self {
        let map = C::new_dense_map(m.sentinel());
        let mut cc1 = CC1::new(map);
        // add builtins
        cc1.nodes.insert(b.true_, Node::new(b.true_));
        cc1.nodes.insert(b.false_, Node::new(b.false_));
        CC{
            b,
            tasks: VecDeque::new(),
            confl: vec!(),
            props: PropagationSet::new(),
            undo: backtrack::Stack::new(),
            traverse: ast::iter_suffix::State::new(m),
            tmp_sig: Signature::new(),
            sig_tbl: backtrack::HashMap::new(),
            expl_st: vec!(),
            cc1,
        }
    }

    #[inline(always)]
    fn find(&self, id: C::AST) -> Repr<C::AST> { self.cc1.find(id) }

    #[inline(always)]
    fn is_root(&self, id: C::AST) -> bool { self.find(id).0 == id }

    /// Add this term to the congruence closure, if not present already.
    fn add_term(&mut self, m: &C::M, t0: C::AST) {
        if self.cc1.nodes.contains(t0) {
            return; // fast path: already there
        }

        self.traverse.clear();

        let CC {traverse, undo, cc1, tasks, ..} = self;
        // traverse in postfix order (shared context: `cc1`)
        traverse.iter(
            t0, m, cc1,
            |_,cc1,t| {
                let enter = !cc1.nodes.contains(t);
                if enter {
                    // avoid entering twice
                    cc1.nodes.insert(t, Node::new(t));
                }
                enter
            },
            |m,cc1,t| {
                debug_assert!(cc1.nodes.contains(t));
                trace!("add-term {}", m.pp(t));
                cc1.nodes.insert(t, Node::new(t));

                // now add itself to its children's list of parents.
                for u in m.view(t).subterms() {
                    debug_assert!(cc1.nodes.contains(u)); // postfix order
                    let parents = cc1.nodes.parents_mut(u);
                    parents.push(t);
                }
                // remove `t` before its children
                undo.push_if_nonzero(UndoOp::RemoveTerm(t));

                if needs_signature(m, t) {
                    tasks.push_back(Task::UpdateSig(t));
                }
            });
    }

    fn map_to_lit(&mut self, t: C::AST, lit: C::B) {
        if ! self.cc1.ok {
            return;
        }

        debug_assert!(self.cc1.nodes.contains(t));
        let n = &mut self.cc1[t];
        if n.as_lit.is_none() {
            debug!("map term {} to literal {:?}", self.m.pp(t), lit);
            n.as_lit = Some(lit);
            self.undo.push_if_nonzero(UndoOp::UnmapLit(t));
        }
    }

    /// Merge `a` and `b`, if they're not already equal.
    fn merge(&mut self, a: C::AST, b: C::AST, expl: Expl<C>) {
        debug_assert!(self.cc1.contains_ast(a));
        debug_assert!(self.cc1.contains_ast(b));

        let mut ra = self.cc1.nodes.find(a);
        let mut rb = self.cc1.nodes.find(b);
        debug_assert!(self.is_root(ra.0), "{}.repr = {}", self.m.pp(a), self.m.pp(ra.0));
        debug_assert!(self.is_root(rb.0), "{}.repr = {}", self.m.pp(b), self.m.pp(rb.0));
        drop(a);
        drop(b);

        if ra == rb {
            return; // done already
        }

        // access the two nodes
        let (na, nb) = self.cc1.nodes.0.get2(ra.0, rb.0);

        // NOTE: would be nice to put `unlikely` there once it stabilizes
        if (na.size as usize) + (nb.size as usize) > u32::MAX as usize {
            panic!("too many terms in one class")
        }

        // merge smaller one into bigger one, except that booleans are
        // always representatives
        if rb.0 == self.b.true_ || rb.0 == self.b.false_ {
            // conflict: merge true with false (since they are distinct)
            if ra.0 == self.b.true_ || ra.0 == self.b.false_ {
                // generate conflict from `expl`, `a == ra`, `b == rb`
                trace!("generate conflict from merge of true/false from {} and {}",
                       self.m.pp(a), self.m.pp(b));
                self.cc1.ok = false;
                self.undo.push_if_nonzero(UndoOp::SetOk);
                {
                    let mut expl = ExplResolve::new(self, expl);
                    expl.explain_eq(a, ra.0);
                    expl.explain_eq(b, rb.0);
                    expl.fixpoint();
                }
                trace!("computed conflict: {:?}", &self.confl);
                return;
            } else {
                // merge into true/false
                std::mem::swap(&mut ra, &mut rb);
            }
        } else if ra.0 == self.b.true_ || ra.0 == self.b.false_ {
            // `ra` must be repr
        } else if na.size < nb.size {
            // swap a and b
            std::mem::swap(&mut ra, &mut rb);
        }
        drop(na);
        drop(nb);

        trace!("merge {} into {}", self.m.pp(rb.0), self.m.pp(ra.0));

        // update forest tree so that `b --[expl]--> a`.
        // Note that here we link `a` and `b`, not their representatives.
        {
            self.undo.push_if_nonzero(UndoOp::RemoveExplLink(a,b));

            self.cc1.reroot_forest(b);
            let nb = &mut self.cc1[b];
            debug_assert!(nb.expl.is_none());
            nb.expl = Some((a, expl));
        }

        // undo the merge on backtrack
        self.undo.push_if_nonzero(UndoOp::Unmerge {
            root: ra, old_root: rb,
        });

        // might need to check for congruence again for parents of `b`,
        // since one of their direct child (b) now has a different
        // representative
        {
            let CC {m, cc1, tasks, ..} = self;
            cc1.nodes.iter_parents(rb, |p_b| {
                if needs_signature(&m, p_b) {
                    tasks.push_back(Task::UpdateSig(p_b));
                }
            });
        }

        // perform actual merge of classes
        // for x in b.class: x.root = a
        let CC {cc1, m, b, props, ..} = self;
        cc1.nodes.iter_class(rb, |n| {
            trace!("{}.iter_class: update {}", m.pp(rb.0), m.pp(n.id));
            debug_assert_eq!(n.root, rb);
            n.root = ra;

            // if a=true/false, and `n` has a literal, propagate the literal
            if ra.0 == b.true_ && n.as_lit.is_some() {
                let lit = n.as_lit.unwrap();
                trace!("propagate literal {:?} (for true≡{})", lit, m.pp(n.id));
                props.propagate(lit);
            } else if ra.0 == b.false_ && n.as_lit.is_some() {
                let lit = ! n.as_lit.unwrap();
                trace!("propagate literal {:?} (for false≡{})", lit, m.pp(n.id));
                props.propagate(lit);
            }
        });

        // ye ole' switcharoo (of doubly linked lists for the equiv class)
        //
        // instead of:  a --> next_a,  b --> next_b
        // have:  a --> next_b, b --> next_a
        //
        {
            // access the two nodes
            let (na, nb) = self.cc1.nodes.0.get2(ra.0, rb.0);

            let next_a = na.next;
            let next_b = nb.next;

            na.size += nb.size;
            na.next = next_b;
            nb.next = next_a;
        }

        // check that the merge went well
        if cfg!(debug) {
            self.cc1.nodes.iter_class(ra, |n| {
                debug_assert_eq!(n.root, ra, "root of cls({:?})", m.pp(ra.0))
            });
        }
    }

    /// Check and update signature of `t`, possibly adding new merged by congruence.
    fn update_signature(&mut self, t: C::AST) {
        let CC {m, tmp_sig: ref mut sig, cc1, sig_tbl, tasks, ..} = self;
        match m.get().view(t) {
            View::Const(_) => (),
            View::App {f, args} if f == self.b.eq => {
                // do not compute a signature, but check if `args[0]==args[1]`
                let a = args[0];
                let b = args[1];
                if self.cc1.nodes.is_eq(a,b) {
                    trace!("merge {} with true by eq-rule", m.pp(t));
                    let expl = Expl::AreEq(a,b);
                    self.tasks.push_back(Task::Merge(t, self.b.true_, expl));
                }
            },
            View::App {f, args} => {
                // compute signature and look for collisions
                compute_app(&mut sig, &cc1, f, args);
                match sig_tbl.get(sig) {
                    None => {
                        // insert into signature table
                        sig_tbl.insert(sig.clone(), t);
                    },
                    Some(u) if t == *u => (),
                    Some(u) => {
                        // collision, merge `t` and `u` as they are congruent
                        trace!("merge by congruence: {} and {}", m.pp(t), m.pp(*u));
                        let expl = Expl::Congruence(t, *u);
                        tasks.push_back(Task::Merge(t, *u, expl));
                    }
                }
            },
        }
    }
}

// query the graph
impl<C:Ctx> CC1<C> {
    fn new(map: C::Map) -> Self {
        CC1 {
            nodes: Nodes::new(map),
            ok: true,
        }
    }

    #[inline(always)]
    fn contains_ast(&self, t: C::AST) -> bool { self.nodes.contains(t) }

    #[inline(always)]
    fn find(&self, t: C::AST) -> Repr<C::AST> { self.nodes.find(t) }

    /// Undo one change.
    fn perform_undo(&mut self, op: UndoOp<C::AST>) {
        trace!("perform-undo {:?}", self.m.pp(&op));
        match op {
            UndoOp::SetOk => {
                debug_assert!(! self.ok);
                self.ok = true;
            },
            UndoOp::Unmerge {root: a, old_root: b} => {
                assert_ne!(a.0,b.0); // crucial invariant

                let (na, nb) = self.nodes.0.get2(a.0, b.0);

                debug_assert_eq!(na.root, a, "root: {}, repr: {}",
                                 self.m.pp(na.root.0), self.m.pp(a.0));
                debug_assert_eq!(nb.root, a);

                debug_assert!(na.size > nb.size);
                na.size -= nb.size;

                // inverse switcharoo
                {
                    let next_a = na.next;
                    let next_b = nb.next;

                    na.next = next_b;
                    nb.next = next_a;
                }
                drop(na);
                drop(nb);

                // restore `root` pointer of all members of `b.class`
                self.nodes.iter_class(b, |nb1| {
                    debug_assert_eq!(nb1.root, a);
                    nb1.root = b;
                });
            },
            UndoOp::RemoveExplLink(a,b) => {
                // one of {a,b} points to the other, explanation wise.
                // Be sure to remove this link from the proof forest.
                {
                    assert_ne!(a,b);
                    let (na, nb) = self.nodes.0.get2(a,b);
                    match nb.expl {
                        Some((ra2,_)) if ra2 == a => nb.expl = None,
                        _ => ()
                    }
                    match na.expl {
                        Some((rb2,_)) if rb2 == b => na.expl = None,
                        _ => ()
                    }
                }
            },
            UndoOp::RemoveTerm(t) => {
                debug_assert_eq!(0, self.nodes[t].parents.len(), "remove term with parents");
                self.nodes.remove(t);

                // remove from children's parents' lists
                let mr = self.m.get();
                for u in mr.view(t).subterms() {
                    let parents = self.nodes.parents_mut(u);
                    debug_assert_eq!(parents.last().cloned(), Some(t));
                    parents.pop();
                }
            }
            UndoOp::UnmapLit(t) => {
                let n = &mut self[t];
                debug_assert!(n.as_lit.is_some());
                n.as_lit = None;
            },
        }
    }

    /// Reroot proof forest for the class of `r` so that `r` is the root.
    fn reroot_forest(&mut self, t: C::AST) {
        trace!("reroot {}", self.m.pp(t));
        let (mut cur_t, mut expl) = {
            let n = &mut self[t];
            match &n.expl {
                None => {
                    return; // rooted in `t` already
                },
                Some((u,e)) => {
                    let tup = (*u,e.clone()).clone();
                    n.expl = None;
                    tup
                }
            }
        };

        let mut prev_t = t;
        loop {
            let cur_node = &mut self[cur_t];
            let mut expl_tup = Some((prev_t,expl));
            // set `cur_node.expl = (prev_t, expl)`
            std::mem::swap(&mut cur_node.expl, &mut expl_tup);
            // `expl_tup` now has `cur_node.expl`'s former value.
            match expl_tup {
                None => break,
                Some((next, expl_next)) => {
                    // follow pointer
                    prev_t = cur_t;
                    cur_t = next;
                    expl = expl_next;
                },
            }
        }
    }

    /// Distance separating `t` from the root of its explanation forest.
    fn dist_to_expl_root(&self, mut t: C::AST) -> usize {
        let mut dist = 0;

        while let Node {expl: Some((next_t,_)), ..} = self[t] {
            dist += 1;
            t = next_t;
        }
        dist
    }

    /// Find the closest common ancestor of `a` and `b` in the proof
    /// forest.
    /// Precond: `is_eq(a,b)`.
    fn find_expl_common_ancestor(&self, mut a: C::AST, mut b: C::AST) -> C::AST {
        debug_assert!(self.nodes.is_eq(a,b));

        let dist_a = self.dist_to_expl_root(a);
        let dist_b = self.dist_to_expl_root(b);
        if dist_a > dist_b {
            a = self.skip_expl_links(a, dist_a - dist_b);
        } else if dist_a < dist_b {
            b = self.skip_expl_links(b, dist_b - dist_a);
        };

        // now walk in lock-step until we find the ancestor
        loop {
            if a == b {
                return a;
            }

            if let Some((a2,_)) = self[a].expl { a = a2 } else { panic!() };
            if let Some((b2,_)) = self[b].expl { b = b2 } else { panic!() };
        }
    }

    /// Skip `n` links in the explanation forest.
    fn skip_expl_links(&self, mut t: C::AST, mut n: usize) -> C::AST {
        while n > 0 {
            if let Some((t2,_)) = self[t].expl { t = t2 } else { panic!() };
            n -= 1
        };
        t
    }
}

impl<C:Ctx> backtrack::Backtrackable for CC<C> {
    fn push_level(&mut self) {
        trace!("push-level");
        self.run_tasks(); // be sure to commit changes before saving
        self.undo.push_level();
        self.sig_tbl.push_level();
    }

    fn pop_levels(&mut self, n: usize) {
        debug_assert_eq!(self.undo.n_levels(), self.sig_tbl.n_levels());
        let cc1 = &mut self.cc1;
        self.undo.pop_levels(n, |op| cc1.perform_undo(op));
        self.sig_tbl.pop_levels(n);
        if n > 0 {
            trace!("pop-levels {}", n);
            self.tasks.clear(); // changes are invalidated
        }
    }

    fn n_levels(&self) -> usize { self.undo.n_levels() }
}

/// Temporary structure to resolve explanations.
struct ExplResolve<'a,C:Ctx> {
    m: &'a C::M,
    cc1: &'a CC1<C>,
    confl: &'a mut Vec<C::B>, // conflict clause to produce
    expl_st: &'a mut Vec<Expl<C>>,
}

impl<'a,C:Ctx> ExplResolve<'a,C> {
    /// Create the temporary structure.
    fn new(cc: &'a mut CC<C>, m: &C::M, e: Expl<C>) -> Self {
        let CC { cc1, confl, expl_st, ..} = cc;
        confl.clear();
        expl_st.clear();
        expl_st.push(e); // start from there
        ExplResolve { m, confl, cc1, expl_st }
    }

    /// Main loop for turning explanations into a conflict
    fn fixpoint(mut self) -> &'a Vec<C::B> {
        let m = &self.m;
        while let Some(e) = self.expl_st.pop() {
            trace!("expand-expl: {}", m.pp(&e));
            match e {
                Expl::Lit(lit) => {
                    self.confl.push(!lit); // conflict needs negation
                },
                Expl::AreEq(a,b) => {
                    self.explain_eq(a, b);
                },
                Expl::Congruence(a,b) => {
                    // explain why arguments are pairwise equal
                    match (m.view(a), m.view(b)) {
                        (View::App {f: f1, args: args1},
                         View::App {f: f2, args: args2}) => {
                            debug_assert_eq!(args1.len(), args2.len());
                            self.explain_eq(f1, f2);
                            for i in 0 .. args1.len() {
                                self.explain_eq(args1[i], args2[i]);
                            }
                        },
                        _ => unreachable!(),
                    }
                }
            }
        }
        // cleanup conflict
        self.confl.sort_unstable();
        self.confl.dedup();
        self.confl
    }

    /// Explain why `a` and `b` were merged, pushing some sub-tasks
    /// onto `self.expl_st`, and leaf literals onto `self.confl`.
    fn explain_eq(&mut self, a: C::AST, b: C::AST) {
        if a == b { return }
        trace!("explain merge of {} and {}", self.m.pp(a), self.m.pp(b));

        let common_ancestor = self.cc1.find_expl_common_ancestor(a, b);
        trace!("common ancestor: {}", self.m.pp(common_ancestor));
        self.explain_along_path(a, common_ancestor);
        self.explain_along_path(b, common_ancestor);
    }

    /// Explain why `cur =_E ancestor`, where `ancestor` is reachable from `cur`
    fn explain_along_path(&mut self, mut cur: C::AST, ancestor: C::AST) {
        while cur != ancestor {
            if let Some((next, expl)) = &self.cc1[cur].expl {
                self.expl_st.push(expl.clone()); // need to explain this link
                cur = *next;
            } else {
                panic!()
            }
        }
    }
}

impl<C:Ctx> Nodes<C> {
    fn new(map: C::Map) -> Self {
        Nodes(map)
    }

    #[inline(always)]
    fn contains(&self, t: C::AST) -> bool { self.0.contains(t) }

    #[inline(always)]
    fn insert(&mut self, t: C::AST, n: Node<C>) {
        self.0.insert(t, n)
    }

    /// Find representative of the given node
    #[inline(always)]
    fn find(&self, id: C::AST) -> Repr<C::AST> { self[id].root }

    /// Are these two terms known to be equal?
    #[inline(always)]
    fn is_eq(&self, a: C::AST, b: C::AST) -> bool {
        self.find(a) == self.find(b)
    }

    #[inline(always)]
    fn parents_mut(&mut self, t: C::AST) -> &mut ParentList<C::B> { &mut self[t].parents }

    #[inline(always)]
    fn remove(&mut self, t: C::AST) {
        self.0.remove(t)
    }

    /// Call `f` with a mutable ref on all nodes of the class of `r`
    fn iter_class<F>(&mut self, r: Repr<C::AST>, mut f: F)
        where F: for<'b> FnMut(&'b mut Node<C>)
    {
        let mut t = r.0;
        loop {
            let n = &mut self[t];
            f(n);

            t = n.next;
            if t == r.0 { break } // done the full loop
        }
    }

    /// Call `f` on all parents of all nodes of the class of `r`
    fn iter_parents<F>(&mut self, r: Repr<C::AST>, mut f: F)
        where F: FnMut(C::AST)
    {
        self.iter_class(r, |n| {
            for &p_b in n.parents.iter() {
                f(p_b)
            }
        });
    }
}

impl<AST> ParentList<AST> {
    fn new() -> Self { ParentList(SVec::new()) }

    #[inline(always)]
    fn len(&self) -> usize { self.0.len() }
}

mod cc {
    use super::*;

    impl<C:Ctx> std::ops::Index<C::AST> for Nodes<C> {
        type Output = Node<C>;
        #[inline(always)]
        fn index(&self, id: C::AST) -> &Self::Output {
            self.0.get(id).unwrap()
        }
    }

    impl<C:Ctx> std::ops::IndexMut<C::AST> for Nodes<C> {
        #[inline(always)]
        fn index_mut(&mut self, id: C::AST) -> &mut Self::Output {
            self.0.get_mut(id).unwrap()
        }
    }

    impl<C:Ctx> std::ops::Index<C::AST> for CC1<C> {
        type Output = Node<C>;
        #[inline(always)]
        fn index(&self, id: C::AST) -> &Self::Output {
            &self.nodes[id]
        }
    }

    impl<C:Ctx> std::ops::IndexMut<C::AST> for CC1<C> {
        #[inline(always)]
        fn index_mut(&mut self, id: C::AST) -> &mut Self::Output {
            &mut self.nodes[id]
        }
    }

    impl<AST> std::ops::Deref for ParentList<AST> {
        type Target = SVec<AST>;
        fn deref(&self) -> &Self::Target { &self.0 }
    }
    impl<AST> std::ops::DerefMut for ParentList<AST> {
        fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
    }
}

// manipulating nodes
mod node {
    use super::*;

    /// The default `node` object
    pub(super) fn sentinel<C:Ctx>() -> Node<C> { Node::new(C::sentinel()) }

    impl<C:Ctx> PartialEq for Node<C> {
        fn eq(&self, other: &Node<C>) -> bool { self.id == other.id }
    }

    impl<C:Ctx> Node<C> {
        /// Create a new node
        pub fn new(id: C::AST) -> Self {
            let parents = ParentList::new();
            Node {
                id, next: id, expl: None, size: 1,
                root: Repr(id), as_lit: None, parents,
            }
        }
    }
}

mod expl {
    use super::*;

    impl<C:Ctx> pp::Pretty1<C::M> for Expl<C> {
        fn pp_with(&self, m: &C::M, ctx: &mut pp::Ctx) {
            match self {
                Expl::Lit(lit) => {
                    ctx.str("lit(").debug(lit).str(")");
                },
                Expl::AreEq(a,b) => {
                    ctx.str("are-eq(").pp(&m.pp(a)).str(", ").pp(&m.pp(b)).str(")");
                }
                Expl::Congruence(a,b) => {
                    ctx.str("congruence(").pp(&m.pp(a)).str(", ").pp(&m.pp(b)).str(")");
                }
            }
        }
    }

    impl<AST, M:Manager> pp::Pretty1<M> for UndoOp<AST> where AST : pp::Pretty1<M> {
        fn pp_with(&self, m: &M, ctx: &mut pp::Ctx) {
            match self {
                UndoOp::SetOk => { ctx.str("set-ok"); },
                UndoOp::Unmerge{root:a,old_root:b} => {
                    ctx.str("unmerge(").pp(&m.pp(a.0)).str(", ").pp(&m.pp(b.0)).str(")");
                },
                UndoOp::RemoveExplLink(a,b) => {
                    ctx.str("remove-expl-link(").pp(&m.pp(a)).str(", ").pp(&m.pp(b)).str(")");
                },
                UndoOp::UnmapLit(t) => {
                    ctx.str("unmap(").pp(&m.pp(t)).str(")");
                },
                UndoOp::RemoveTerm(t) => {
                    ctx.str("remove-term(").pp(&m.pp(t)).str(")");
                }
            }
        }
    }
}

impl<AST:Eq+Hash+Debug> Signature<AST> {
    /// Create a new signature.
    fn new() -> Self { Signature(SVec::new()) }

    /// Clear the signature's content.
    #[inline(always)]
    fn clear(&mut self) { self.0.clear() }
}

fn compute_app<C:Ctx>(
    &mut sig: Signature<C::AST>, cc1: &CC1<C>, f: &C::AST, args: &[C::AST]
) {
    sig.clear();
    sig.0.push(cc1.find(f));
    for &u in args {
        sig.0.push(cc1.find(u));
    }
}

