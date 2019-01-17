
//! Congruence closure.
//!
//! The `CC` type is responsible for enforcing congruence and transitivity
//! of equality.

// TODO: parametrize by "micro theories" (which just work on merges + expl)

// micro theories:
// - rule for `not` (t == true |- not t == false, and conversely)
// - rule for `ite` (t == true |- not t == false, and conversely)

// TODO(perf): backtrackable array allocator for signatures
// TODO(perf): sparse map for nodes (using a second dense array)?

use {
    std::{ u32, ptr, hash::Hash, fmt::Debug, },
    batsmt_core::{backtrack, },
    fxhash::FxHashMap,
    batsmt_pretty as pp,
    crate::{ Ctx, Actions, CCInterface, CCView, SVec, pp_t, },
};

enum TraverseTask<AST> {
    Enter(AST),
    Exit(AST,NodeID)
}

/// The congruence closure.
pub struct CC<C:Ctx> {
    n_true: NodeID,
    n_false: NodeID,
    pending: Vec<NodeID>, // update signatures
    combine: Vec<(NodeID,NodeID,Expl<C::B>)>, // merge
    undo: backtrack::Stack<UndoOp>,
    props: Vec<C::B>, // local for propagations
    expl_st: Vec<Expl<C::B>>, // to expand explanations
    tmp_sig: Signature<C::Fun>, // for computing signatures
    traverse: Vec<TraverseTask<C::AST>>, // for adding terms
    sig_tbl: backtrack::HashMap<Signature<C::Fun>, NodeID>,
    lit_expl: backtrack::HashMap<C::B, LitExpl<C::B>>, // pre-explanations for propagations
    cc1: CC1<C>,
}

/// internal state, with just the core structure for nodes and parent sets
struct CC1<C:Ctx> {
    ok: bool, // no conflict?
    alloc_parent_list: ListAlloc<NodeID>,
    nodes: Nodes<C>,
    confl: Vec<C::B>, // local for conflict
}

/// Explanation for the propagation of a boolean literal.
#[derive(Debug)]
enum LitExpl<B> {
    Propagated {
        // we propagated it from given merges
        eqns: [(NodeID,NodeID); 2],
        expl: Expl<B>,
    },
}

/// Unique Node ID.
#[derive(Debug,Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd)]
struct NodeID(u32);

/// Map terms into the corresponding node.
struct Nodes<C:Ctx>{
    n_true: NodeID,
    n_false: NodeID,
    map: FxHashMap<C::AST, NodeID>,
    nodes: Vec<Node<C>>,
    find_stack: Vec<NodeID>,
}

#[allow(type_alias_bounds)]
type Node<C:Ctx> = NodeDef<C::AST, C::B>;

/// One node in the congruence closure's E-graph.
///
/// It contains:
/// - the term itself
/// - a direct pointer to the class' root
/// - pointer to next element of the class (circular list)
/// - a linked list of parent terms
/// - the proof forest pointer
/// - an optional mapping from the term to a boolean literal (for propagation)
#[derive(Clone)]
struct NodeDef<AST, B> where AST : Sized, B : Sized {
    id: NodeID,
    ast: AST, // what AST does this correspond to?
    next: NodeID, // next elt in class
    expl: Option<(NodeID, Expl<B>)>, // proof forest
    as_lit: Option<B>, // if this term corresponds to a boolean literal
    root: Repr, // current representative (initially, itself)
    parents: List<NodeID>,
    flags: u8, // boolean flags
}

/// A node in a singly-linked list of objects.
#[derive(Copy,Clone)]
struct ListC<T>(T, *mut ListC<T>);

type ListAlloc<T> = backtrack::Alloc<ListC<T>>;

/// A singly-linked list of T.
#[derive(Clone)]
struct List<T> {
    first: *mut ListC<T>, // first node (null iff len==0)
    last: *mut ListC<T>, // last node (null iff len==0)
    len: u32, // number of nodes
}

/// A representative
#[derive(Debug,Clone,Copy,Eq,PartialEq,Hash,Ord,PartialOrd)]
struct Repr(NodeID);

/// An explanation for a merge
#[derive(Clone,Debug)]
enum Expl<B> {
    Lit(B), // because literal was asserted
    Congruence(NodeID, NodeID), // because terms are congruent
    AreEq(NodeID, NodeID), // because terms are equal
}

/// Undo operations on the congruence closure
#[derive(Debug)]
enum UndoOp {
    SetOk,
    RemoveNode(NodeID),
    UnmapLit(NodeID),
    Unmerge {
        root: Repr, // the new repr
        old_root: Repr, // merged into `a`
    }, // unmerge these two reprs
    RemoveExplLink(NodeID,NodeID), // remove explanation link connecting these
}

/// A signature for a term, obtained by replacing its subterms with their repr.
///
/// Signatures have the properties that if two terms are congruent,
/// then their signatures are identical.
#[derive(Eq,PartialEq,Hash,Clone,Debug)]
struct Signature<F> {
    f: Option<F>,
    subs: SVec<Repr>
}

// implement main interface
impl<C:Ctx> CCInterface<C> for CC<C> {
    fn merge(&mut self, m: &C, t1: C::AST, t2: C::AST, lit: C::B) {
        debug!("merge {} and {} (expl {:?})", pp_t(m,&t1), pp_t(m,&t2), lit);
        // FIXME debug!("merge {} and {} (expl {:?})", pp_term(m,&t1), pp_term(m,&t2), lit);
        let n1 = self.add_term(m, t1);
        let n2 = self.add_term(m, t2);
        let expl = Expl::Lit(lit);
        self.combine.push((n1,n2,expl));
    }

    fn distinct(&mut self, _m: &C, _ts: &[C::AST], _lit: C::B) {
        unimplemented!("distinct is not supported yet")
        /*
        let mut v = SVec::with_capacity(ts.len());
        v.extend_from_slice(ts);
        let expl = Expl::Lit(lit);
        self.tasks.push_back(Task::Distinct(v,expl))
        */
    }

    fn add_literal(&mut self, m: &C, t: C::AST, lit: C::B) {
        let n = self.add_term(m, t);
        self.map_to_lit(m, n, lit);
    }

    #[inline]
    fn final_check<A>(&mut self, m: &C, acts: &mut A)
        where A: Actions<C>
    {
        self.check_internal(m, acts)
    }

    #[inline]
    fn partial_check<A>(&mut self, m: &C, acts: &mut A)
        where A: Actions<C>
    {
        self.check_internal(m, acts)
    }

    fn explain_prop(&mut self, m: &C, p: C::B) -> &[C::B] {
        trace!("explain prop {:?}", p);
        let e = self.lit_expl.get(&p).expect("no explanation recorded");
        trace!("pre-explanation is {:?}", e);
        match e {
            LitExpl::Propagated{eqns,expl} => {
                let mut er = ExplResolve::new(&mut self.cc1, &mut self.expl_st);
                er.add_expl(expl.clone());
                for (a,b) in eqns.iter() {
                    er.explain_eq(m, *a, *b)
                }
                er.fixpoint(m);
                trace!("... final explanation: {:?}", &self.cc1.confl[..]);
                &self.cc1.confl[..]
            },
        }
    }

    fn has_partial_check() -> bool { true }

    fn impl_descr() -> &'static str { "fast congruence closure"}
}

impl<C:Ctx> CC<C> {
    // main `check` function, performs the fixpoint
    fn check_internal<A>(&mut self, m: &C, acts: &mut A)
        where A: Actions<C>
    {
        debug!("check-internal (pending: {}, combine: {})",
            self.pending.len(), self.combine.len());
        self.fixpoint(m);
        if self.cc1.ok {
            for &p in &self.props {
                self.cc1.ok = self.cc1.ok && acts.propagate(p);
            }
        } else {
            debug_assert!(self.cc1.confl.len() >= 1); // must have some conflict
            let costly = true;
            acts.raise_conflict(&self.cc1.confl, costly)
        }
        self.props.clear();
    }

    /// Main CC algorithm.
    fn fixpoint(&mut self, m: &C) {
        let CC{
            combine,cc1,pending, expl_st,undo,tmp_sig,
            sig_tbl,props,lit_expl,n_true,n_false,..} = self;
        loop {
            if !cc1.ok {
                combine.clear();
                pending.clear();
                break
            }

            {
                let mut updsig = UpdateSigPhase{cc1,combine,sig_tbl,tmp_sig};
                for &t in pending.iter() {
                    if updsig.cc1[t].needs_sig() {
                        updsig.update_signature(m, t);
                    }
                }
                pending.clear();
            }

            {
                let mut merger = MergePhase{
                    cc1,pending,expl_st,undo,props,lit_expl,
                    n_true: *n_true,n_false: *n_false};
                for (t,u,expl) in combine.iter() {
                    merger.merge(m,*t,*u,expl.clone())
                }
                combine.clear();
            }

            if pending.is_empty() {
                break; // done
            }
        }
    }
}

// main congruence closure operations
impl<C:Ctx> CC<C> {
    /// Create a new congruence closure.
    pub fn new(m: &mut C) -> Self {
        let mut cc1 = CC1::new();
        // add builtins
        let true_ = m.get_bool_term(true);
        let false_ = m.get_bool_term(false);
        debug_assert_ne!(true_, false_);
        let n_true = cc1.nodes.insert(true_);
        let n_false = cc1.nodes.insert(false_);
        cc1.nodes.n_true = n_true;
        cc1.nodes.n_false = n_false;
        CC{
            n_true, n_false,
            pending: vec!(),
            combine: vec!(),
            props: vec!(),
            undo: backtrack::Stack::new(),
            traverse: vec!(),
            tmp_sig: Signature::new(),
            sig_tbl: backtrack::HashMap::new(),
            expl_st: vec!(),
            lit_expl: backtrack::HashMap::new(),
            cc1,
        }
    }

    /// Add this term to the congruence closure, if not present already.
    #[inline]
    fn add_term(&mut self, m: &C, t0: C::AST) -> NodeID {
        match self.cc1.nodes.map.get(&t0) {
            Some(n) => *n,
            None => self.add_term_rec(m, t0),
        }
    }

    fn add_term_rec(&mut self, m: &C, t0: C::AST) -> NodeID {
        self.traverse.clear();

        let CC {traverse, undo, cc1, pending, ..} = self;
        // traverse in postfix order (shared context: `cc1`)

        traverse.push(TraverseTask::Enter(t0));
        let mut n0 = None;
        while let Some(task) = traverse.pop() {
            match task {
                TraverseTask::Enter(t) => {
                    if ! cc1.nodes.contains(&t) {
                        let n = cc1.nodes.insert(t);

                        if t == t0 { n0 = Some(n) } // first node

                        traverse.push(TraverseTask::Exit(t,n));
                        // add subterms
                        m.view_as_cc_term(&t).iter_subterms(|u| {
                            traverse.push(TraverseTask::Enter(*u))
                        });
                    }
                },
                TraverseTask::Exit(t,n) => {
                    // now add itself to its children's list of parents.
                    let view = m.view_as_cc_term(&t);
                    view.iter_subterms(|u| {
                        debug_assert!(cc1.nodes.contains(&u)); // postfix order
                        let ur = cc1.find_t(*u);
                        let parents = cc1.nodes.parents_mut(ur.0);
                        parents.add(&mut cc1.alloc_parent_list, n);
                    });
                    // remove `t` before its children
                    undo.push_if_nonzero(UndoOp::RemoveNode(n));

                    if view.needs_sig() {
                        cc1.nodes[n].set_needs_sig();
                        pending.push(n);
                    }
                },
            }
        }
        assert!(n0.is_some());
        n0.unwrap()
    }

    fn map_to_lit(&mut self, m: &C, t: NodeID, lit: C::B) {
        if ! self.cc1.ok {
            return;
        }

        let n = &mut self.cc1[t];
        if n.as_lit.is_none() {
            n.as_lit = Some(lit);
            debug!("map term {} to literal {:?}", pp::pp2(self,m,&t), lit);
            self.undo.push_if_nonzero(UndoOp::UnmapLit(t));
        }
    }
}

struct MergePhase<'a,C:Ctx> {
    cc1: &'a mut CC1<C>,
    n_true: NodeID,
    n_false: NodeID,
    pending: &'a mut Vec<NodeID>,
    expl_st: &'a mut Vec<Expl<C::B>>,
    undo: &'a mut backtrack::Stack<UndoOp>,
    props: &'a mut Vec<C::B>, // local for propagations
    lit_expl: &'a mut backtrack::HashMap<C::B, LitExpl<C::B>>, // pre-explanations for propagations
}

struct UpdateSigPhase<'a,C:Ctx> {
    cc1: &'a mut CC1<C>,
    combine: &'a mut Vec<(NodeID,NodeID,Expl<C::B>)>,
    sig_tbl: &'a mut backtrack::HashMap<Signature<C::Fun>, NodeID>,
    tmp_sig: &'a mut Signature<C::Fun>,
}

impl<'a, C:Ctx> MergePhase<'a,C> {
    /// Merge `a` and `b`, if they're not already equal.
    fn merge(&mut self, m: &C, mut a: NodeID, mut b: NodeID, expl: Expl<C::B>) {
        let mut ra = self.cc1.nodes.find(a);
        let mut rb = self.cc1.nodes.find(b);
        debug_assert!(self.cc1.is_root(ra.0), "{}.repr = {}",
            pp::pp2(self.cc1,m,&a), pp::pp2(self.cc1,m,&ra.0));
        debug_assert!(self.cc1.is_root(rb.0), "{}.repr = {}",
            pp::pp2(self.cc1,m,&b), pp::pp2(self.cc1,m,&rb.0));
        // debug_assert!(self.cc1.is_root(ra.0), "{}.repr = {}", pp_term(m,&a), pp_term(m,&ra.0));
        // debug_assert!(self.cc1.is_root(rb.0), "{}.repr = {}", pp_term(m,&b), pp_term(m,&rb.0));

        if ra == rb {
            return; // done already
        }

        // access the two nodes
        let (na, nb) = self.cc1.nodes.get2(ra.0, rb.0);

        // NOTE: would be nice to put `unlikely` there once it stabilizes
        if na.len() + nb.len() > u32::MAX as usize {
            panic!("too many terms in one class")
        }

        // merge smaller one into bigger one, except that booleans are
        // always representatives
        if rb.0 == self.n_true || rb.0 == self.n_false {
            // conflict: merge true with false (since they are distinct)
            if ra.0 == self.n_true || ra.0 == self.n_false {
                // generate conflict from `expl`, `a == ra`, `b == rb`
                trace!("generate conflict from merge of true/false from {} and {}",
                       pp::pp2(self.cc1,m,&a), pp::pp2(self.cc1,m,&b));
                assert_ne!(ra.0, rb.0);
                self.cc1.ok = false;
                self.undo.push_if_nonzero(UndoOp::SetOk);
                {
                    let mut er = ExplResolve::new(&mut self.cc1, &mut self.expl_st);
                    er.add_expl(expl);
                    er.explain_eq(m, a, ra.0);
                    er.explain_eq(m, b, rb.0);
                    er.fixpoint(m);
                }
                // negation
                for lit in self.cc1.confl.iter_mut() { *lit = ! *lit }
                trace!("inconsistent set of explanations: {:?}", &self.cc1.confl);
                return;
            } else {
                // merge into true/false, not the other way around
                std::mem::swap(&mut ra, &mut rb);
            }
        } else if ra.0 == self.n_true || ra.0 == self.n_false {
            // `ra` must be repr
        } else if na.len() < nb.len() {
            // swap a and b
            std::mem::swap(&mut ra, &mut rb);
            std::mem::swap(&mut a, &mut b);
        }
        drop(na);
        drop(nb);

        trace!("merge {} into {}", pp::pp2(self.cc1,m,&rb.0), pp::pp2(self.cc1,m,&ra.0));

        // update forest tree so that `b --[expl]--> a`.
        // Note that here we link `a` and `b`, not their representatives.
        {
            self.undo.push_if_nonzero(UndoOp::RemoveExplLink(a,b));

            self.cc1.reroot_forest(m, b);
            let nb = &mut self.cc1[b];
            debug_assert!(nb.expl.is_none());
            nb.expl = Some((a, expl.clone()));
        }

        // undo the merge on backtrack
        self.undo.push_if_nonzero(UndoOp::Unmerge {
            root: ra, old_root: rb,
        });

        // might need to check for congruence again for parents of `b`,
        // since one of their direct child (b) now has a different
        // representative
        {
            let MergePhase{cc1, pending, ..} = self;
            cc1.nodes.iter_parents(rb, |p_b| {
                pending.push(*p_b)
            });
        }

        let MergePhase{cc1, props, lit_expl, n_true, n_false, ..} = self;

        // if ra is {true,false}, propagate lits
        if ra.0 == cc1.nodes.n_true || ra.0 == cc1.nodes.n_false {
            trace!("{}.class: look for propagations", pp::pp2(*cc1,m,&rb.0));
            let rb_t = cc1[rb.0].ast;
            cc1.nodes.iter_class(rb, |n| {
                trace!("... {}.iter_class: check {}", pp_t(m,&rb_t), pp_t(m,&n.ast));
                n.root = ra; // while we're there, we can merge eagerly.

                // if a=true/false, and `n` has a literal, propagate the literal
                // assuming it's not known to be true already.
                if let Some(mut lit) = n.as_lit {
                    if !lit_expl.contains_key(&lit) {
                        // future expl: `n=b=a=ra` (where ra∈{true,false})
                        let e = LitExpl::Propagated {
                            expl: expl.clone(),
                            eqns:[(n.id, b), (a, ra.0)],
                        };
                        if ra.0 == *n_true {
                            trace!("propagate literal {:?} (for true≡{}, {:?})",
                                lit, pp_t(m,&n.ast), &expl);
                            props.push(lit);
                        } else {
                            debug_assert_eq!(ra.0, *n_false);
                            lit = !lit;
                            trace!("propagate literal {:?} (for false≡{}, {:?})",
                                lit, pp_t(m,&n.ast), &expl);
                            props.push(lit);
                        }
                        lit_expl.insert(lit, e);
                    }
                }
            });
        }

        // set `rb.root` to `ra`
        cc1[rb.0].root = ra;

        // ye ole' switcharoo (of doubly linked lists for the equiv class)
        //
        // instead of:  a --> next_a,  b --> next_b
        // have:  a --> next_b, b --> next_a
        //
        {
            // access the two nodes, again
            let (na, nb) = self.cc1.nodes.get2(ra.0, rb.0);

            let next_a = na.next;
            let next_b = nb.next;

            na.next = next_b;
            nb.next = next_a;

            // also merge parent lists
            na.parents.append(&mut nb.parents)
        }
    }
}

impl<'a, C:Ctx> UpdateSigPhase<'a,C> {
    /// Check and update signature of `t`, possibly adding new merged by congruence.
    fn update_signature(&mut self, m: &C, n: NodeID) {
        let UpdateSigPhase{tmp_sig: ref mut sig, cc1, sig_tbl, combine, ..} = self;
        let t = cc1[n].ast;
        let has_sig = match m.view_as_cc_term(&t) {
            CCView::Bool(_) | CCView::Opaque(_) | CCView::Distinct(_) => false,
            CCView::Eq(a,b) => {
                // do not compute a signature, but check if `args[0]==args[1]`
                // TODO: store View<NodeID> directly in the nodes, to avoid this step
                let a = cc1.nodes.get_term_id(&a);
                let b = cc1.nodes.get_term_id(&b);
                if cc1.nodes.is_eq(a,b) {
                    trace!("merge {} with true by eq-rule", pp_t(m,&t));
                    let expl = Expl::AreEq(a,b);
                    combine.push((n, cc1.nodes.n_true, expl))
                }
                false
            },
            CCView::Apply(f, args) => {
                // compute signature and look for collisions
                sig.compute_app(cc1, &f, args);
                true
            },
            CCView::ApplyHO(f, args) => {
                sig.compute_app_ho(cc1, f, args);
                true
            },
        };
        if has_sig {
            match sig_tbl.get(sig) {
                None => {
                    // insert into signature table
                    sig_tbl.insert(sig.clone(), n);
                },
                Some(u) if n == *u => (), // same node
                Some(u) => {
                    // collision, merge `t` and `u` as they are congruent
                    trace!("merge by congruence: {} and {}", pp_t(m,&t), pp::pp2(*cc1,m,u));
                    let expl = Expl::Congruence(n, *u);
                    combine.push((n, *u, expl))
                }
            }
        }
    }
}

// query the graph
impl<C:Ctx> CC1<C> {
    fn new() -> Self {
        CC1 {
            nodes: Nodes::new(),
            ok: true,
            alloc_parent_list: backtrack::Alloc::new(),
            confl: vec!(),
        }
    }

    #[inline(always)]
    fn find(&mut self, t: NodeID) -> Repr { self.nodes.find(t) }

    #[inline(always)]
    fn find_t(&mut self, t: C::AST) -> Repr { self.nodes.find_t(t) }

    #[inline(always)]
    fn is_root(&mut self, id: NodeID) -> bool { self.find(id).0 == id }

    /// Undo one change.
    fn perform_undo(&mut self, m: &C, op: UndoOp) {
        trace!("perform-undo {}", pp::pp2(&self.nodes,m,&op));
        match op {
            UndoOp::SetOk => {
                self.ok = true;
                self.confl.clear();
            },
            UndoOp::Unmerge {root: a, old_root: b} => {
                assert_ne!(a.0,b.0); // crucial invariant

                let (na, nb) = self.nodes.get2(a.0, b.0);

                // inverse switcharoo for the class linked lists
                {
                    let next_a = na.next;
                    let next_b = nb.next;

                    na.next = next_b;
                    nb.next = next_a;

                    na.parents.un_append(&mut nb.parents);
                }

                // reset `root` pointer for `nb`
                // reset root for the classes of terms that are now repr again,
                // if they haven't been removed.
                self.nodes.iter_class(b, |nb1| {
                    nb1.root = b;
                });
            },
            UndoOp::RemoveExplLink(a,b) => {
                // one of {a,b} points to the other, explanation wise.
                // Be sure to remove this link from the proof forest.
                {
                    assert_ne!(a,b);
                    let (na, nb) = self.nodes.get2(a,b);
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
            UndoOp::RemoveNode(n) => {
                debug_assert_eq!(0, self.nodes[n].parents.len(), "remove term with parents");
                let t = self.nodes[n].ast;
                self.nodes.remove(n);

                // remove from children's parents' lists
                m.view_as_cc_term(&t).iter_subterms(|u| {
                    let ur = self.find_t(*u);
                    let parents = self.nodes.parents_mut(ur.0);
                    let _n = parents.remove();
                    debug_assert_eq!(_n, n);
                });
            }
            UndoOp::UnmapLit(t) => {
                let n = &mut self[t];
                debug_assert!(n.as_lit.is_some());
                n.as_lit = None;
            },
        }
    }

    /// Reroot proof forest for the class of `r` so that `r` is the root.
    fn reroot_forest(&mut self, m: &C, t: NodeID) {
        trace!("reroot-forest-to {}", pp::pp2(self,m,&t));
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
    fn dist_to_expl_root(&self, mut t: NodeID) -> usize {
        let mut dist = 0;

        while let NodeDef {expl: Some((next_t,_)), ..} = self[t] {
            dist += 1;
            t = next_t;
        }
        dist
    }

    /// Find the closest common ancestor of `a` and `b` in the proof
    /// forest.
    /// Precond: `is_eq(a,b)`.
    fn find_expl_common_ancestor(&mut self, mut a: NodeID, mut b: NodeID) -> NodeID {
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
    fn skip_expl_links(&self, mut t: NodeID, mut n: usize) -> NodeID {
        while n > 0 {
            if let Some((t2,_)) = self[t].expl { t = t2 } else { panic!() };
            n -= 1
        };
        t
    }
}

impl<C:Ctx> backtrack::Backtrackable<C> for CC<C> {
    fn push_level(&mut self, m: &mut C) {
        trace!("push-level");
        self.fixpoint(m); // be sure to commit changes before saving
        self.undo.push_level();
        self.sig_tbl.push_level();
        self.cc1.alloc_parent_list.push_level();
        self.lit_expl.push_level();
    }

    fn pop_levels(&mut self, m: &mut C, n: usize) {
        debug_assert_eq!(self.undo.n_levels(), self.sig_tbl.n_levels());
        debug_assert_eq!(self.undo.n_levels(), self.cc1.alloc_parent_list.n_levels());
        if n > 0 {
            trace!("pop-levels {}", n);
            let cc1 = &mut self.cc1;
            self.undo.pop_levels(n, |op| cc1.perform_undo(m, op));
            self.sig_tbl.pop_levels(n);
            cc1.alloc_parent_list.pop_levels(n);
            self.lit_expl.pop_levels(n);
            self.props.clear();
            self.pending.clear();
            self.combine.clear();
        }
    }

    #[inline(always)]
    fn n_levels(&self) -> usize { self.undo.n_levels() }
}

/// Temporary structure to resolve explanations.
struct ExplResolve<'a,C:Ctx> {
    cc1: &'a mut CC1<C>,
    expl_st: &'a mut Vec<Expl<C::B>>,
}

impl<'a,C:Ctx> ExplResolve<'a,C> {
    /// Create the temporary structure.
    fn new(cc1: &'a mut CC1<C>, expl_st: &'a mut Vec<Expl<C::B>>) -> Self {
        expl_st.clear();
        cc1.confl.clear();
        ExplResolve { cc1, expl_st }
    }

    fn add_expl(&mut self, e: Expl<C::B>) {
        self.expl_st.push(e)
    }

    /// Main loop for turning explanations into a conflict.
    ///
    /// Pushes the resulting literals into `self.cc1.confl`.
    fn fixpoint(mut self, m: &C) -> &'a Vec<C::B> {
        while let Some(e) = self.expl_st.pop() {
            trace!("expand-expl: {}", pp::pp2(&self.cc1.nodes, m, &e));
            match e {
                Expl::Lit(lit) => {
                    self.cc1.confl.push(lit);
                },
                Expl::AreEq(a,b) => {
                    self.explain_eq(m, a, b);
                },
                Expl::Congruence(a,b) => {
                    // explain why arguments are pairwise equal
                    let a = self.cc1[a].ast;
                    let b = self.cc1[b].ast;
                    match (m.view_as_cc_term(&a), m.view_as_cc_term(&b)) {
                        (CCView::Apply(f1, args1), CCView::Apply(f2, args2)) =>
                        {
                            debug_assert_eq!(f1, f2);
                            for i in 0 .. args1.len() {
                                self.explain_eq_t(m, &args1[i], &args2[i]);
                            }
                        },
                        (CCView::ApplyHO(f1, args1), CCView::ApplyHO(f2, args2)) =>
                        {
                            debug_assert_eq!(args1.len(), args2.len());
                            self.explain_eq_t(m, f1, f2);
                            for i in 0 .. args1.len() {
                                self.explain_eq_t(m, &args1[i], &args2[i]);
                            }
                        },
                        _ => unreachable!(),
                    }
                }
            }
        }
        // cleanup conflict
        self.cc1.confl.sort_unstable();
        self.cc1.confl.dedup();
        &self.cc1.confl
    }

    /// Explain why `a` and `b` were merged, pushing some sub-tasks
    /// onto `self.expl_st`, and leaf literals onto `self.confl`.
    fn explain_eq(&mut self, m: &C, a: NodeID, b: NodeID) {
        if a == b { return }
        trace!("explain eq of {} and {}", pp::pp2(self.cc1,m,&a), pp::pp2(self.cc1,m,&b));

        let common_ancestor = self.cc1.find_expl_common_ancestor(a, b);
        trace!("common ancestor: {}", pp::pp2(self.cc1,m,&common_ancestor));
        self.explain_along_path(a, common_ancestor);
        self.explain_along_path(b, common_ancestor);
    }

    fn explain_eq_t(&mut self, m: &C, a: &C::AST, b: &C::AST) {
        let na = self.cc1.nodes.get_term_id(a);
        let nb = self.cc1.nodes.get_term_id(b);
        self.explain_eq(m, na, nb);
    }

    /// Explain why `cur =_E ancestor`, where `ancestor` is reachable from `cur`
    fn explain_along_path(&mut self, mut cur: NodeID, ancestor: NodeID) {
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
    fn new() -> Self {
        Nodes{
            n_true: NodeID::UNDEF,
            n_false: NodeID::UNDEF,
            map: FxHashMap::default(),
            nodes: vec!(),
            find_stack: vec!(),
        }
    }

    #[inline(always)]
    fn contains(&self, t: &C::AST) -> bool { self.map.contains_key(t) }

    /// Find the ID of the given term.
    #[inline]
    fn get_term_id(&self, t: &C::AST) -> NodeID {
        debug_assert!(self.contains(t));
        self.map[t]
    }

    /// Allocate and insert a new node.
    fn insert(&mut self, t: C::AST) -> NodeID {
        let id = {
            let id = self.nodes.len();
            if id >= u32::MAX as usize { panic!("cannot allocate more nodes") }
            NodeID(id as u32)
        };
        let n = NodeDef::new(t, id);
        self.map.insert(t, id);
        self.nodes.push(n);
        debug_assert_eq!(self.get_term_id(&t), id); // next time will give the same
        id
    }

    /// Find the representative of the given term.
    #[inline]
    fn find_t(&mut self, t: C::AST) -> Repr {
        let n = self.get_term_id(&t);
        self.find(n)
    }

    /// Find representative of the given node
    #[inline(always)]
    fn find(&mut self, t: NodeID) -> Repr {
        let root = self[t].root;

        if root.0 == t {
            root // fast path
        } else {
            let root = self.find_rec(root.0, 16); // use recursion
            self[t].root = root; // update this pointer
            root
        }
    }

    // find + path compression, using recursion up to `limit`
    fn find_rec(&mut self, t: NodeID, limit: usize) -> Repr {
        let root = self[t].root;
        if root.0 == t {
            root
        } else {
            // recurse
            let root = {
                if limit == 0 {
                    self.find_loop(root.0)
                } else {
                    self.find_rec(root.0, limit-1)
                }
            };
            self[t].root = root;
            root
        }
    }

    // find + path compression, using a loop
    fn find_loop(&mut self, mut t: NodeID) -> Repr {
        debug_assert_eq!(self.find_stack.len(), 0);

        let root = loop {
            let root = self[t].root;
            if t == root.0 {
                break root
            } else {
                // seek further
                self.find_stack.push(t);
                t = root.0
            }
        };

        // update root pointers (path compression)
        for &u in self.find_stack.iter() {
            self.nodes[u.0 as usize].root = root;
        }
        self.find_stack.clear();

        root
    }

    /// Are these two terms known to be equal?
    #[inline(always)]
    fn is_eq(&mut self, a: NodeID, b: NodeID) -> bool {
        self.find(a) == self.find(b)
    }

    #[inline(always)]
    fn parents_mut(&mut self, t: NodeID) -> &mut List<NodeID> { &mut self[t].parents }

    fn remove(&mut self, t: NodeID) {
        assert_eq!(t.0 as usize, self.nodes.len()-1); // must be the last node
        let ast = self[t].ast;
        self.nodes.pop();
        self.map.remove(&ast);
    }

    /// Access mutably two distinct nodes.
    fn get2(&mut self, t1: NodeID, t2: NodeID) -> (&mut Node<C>, &mut Node<C>) {
        assert_ne!(t1, t2);

        let ref1 = (&mut self.nodes[t1.0 as usize]) as *mut _;
        let ref2 = (&mut self.nodes[t2.0 as usize]) as *mut _;
        // this is correct because t1 != t2, so the pointers are disjoint.
        unsafe { (&mut* ref1, &mut *ref2) }
    }

    /// Call `f` with a mutable ref on all nodes of the class of `r`
    fn iter_class<F>(&mut self, r: Repr, mut f: F)
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
    #[inline]
    fn iter_parents<F>(&mut self, r: Repr, f: F)
        where F: FnMut(&NodeID)
    {
        self[r.0].parents.for_each(f);
    }
}

mod cc {
    use super::*;

    impl<C:Ctx> std::ops::Index<NodeID> for Nodes<C> {
        type Output = Node<C>;
        #[inline(always)]
        fn index(&self, id: NodeID) -> &Self::Output {
            &self.nodes[id.0 as usize]
        }
    }

    impl<C:Ctx> std::ops::IndexMut<NodeID> for Nodes<C> {
        #[inline(always)]
        fn index_mut(&mut self, id: NodeID) -> &mut Self::Output {
            &mut self.nodes[id.0 as usize]
        }
    }

    impl<C:Ctx> std::ops::Index<NodeID> for CC1<C> {
        type Output = Node<C>;
        #[inline(always)]
        fn index(&self, id: NodeID) -> &Self::Output {
            &self.nodes[id]
        }
    }

    impl<C:Ctx> std::ops::IndexMut<NodeID> for CC1<C> {
        #[inline(always)]
        fn index_mut(&mut self, id: NodeID) -> &mut Self::Output {
            &mut self.nodes[id]
        }
    }

    impl<C:Ctx> pp::Pretty2<C, NodeID> for Nodes<C> {
        fn pp2_into(&self, m: &C, n: &NodeID, ctx: &mut pp::Ctx) {
            let t = self[*n].ast;
            ctx.pp(&pp_t(m, &t));
        }
    }

    impl<C:Ctx> pp::Pretty2<C, NodeID> for CC1<C> {
        fn pp2_into(&self, m: &C, n: &NodeID, ctx: &mut pp::Ctx) {
            self.nodes.pp2_into(m,n,ctx)
        }
    }

    impl<C:Ctx> pp::Pretty2<C, NodeID> for CC<C> {
        fn pp2_into(&self, m: &C, n: &NodeID, ctx: &mut pp::Ctx) {
            self.cc1.pp2_into(m,n,ctx)
        }
    }
}

// manipulating nodes
mod node {
    use super::*;

    impl NodeID {
        pub const UNDEF : NodeID = NodeID(u32::MAX);
    }

    impl<AST:Eq, B> PartialEq for NodeDef<AST, B> {
        fn eq(&self, other: &NodeDef<AST, B>) -> bool { self.id == other.id }
    }

    const FLG_NEEDS_SIG : u8 = 0b1;

    impl<AST, B> NodeDef<AST, B> {
        /// Create a new node with the given ID and AST.
        pub fn new(ast: AST, id: NodeID) -> Self {
            let parents = List::new();
            NodeDef {
                id, ast, next: id, expl: None,
                root: Repr(id), as_lit: None, parents, flags: 0,
            }
        }

        #[inline(always)]
        pub fn len(&self) -> usize {
            self.parents.len()
        }

        #[inline]
        pub fn needs_sig(&self) -> bool { (self.flags & FLG_NEEDS_SIG) != 0 }

        #[inline]
        pub fn set_needs_sig(&mut self) { self.flags |= FLG_NEEDS_SIG }
    }
}

mod expl {
    use super::*;

    impl<C:Ctx> pp::Pretty2<C, Expl<C::B>> for Nodes<C> {
        fn pp2_into(&self, m: &C, expl: &Expl<C::B>, ctx: &mut pp::Ctx) {
            match expl {
                Expl::Lit(lit) => {
                    ctx.str("lit(").debug(lit).str(")");
                },
                Expl::AreEq(a,b) => {
                    let a = self[*a].ast;
                    let b = self[*b].ast;
                    ctx.str("are-eq(").pp(&pp_t(m,&a)).str(", ").pp(&pp_t(m,&b)).str(")");
                }
                Expl::Congruence(a,b) => {
                    let a = self[*a].ast;
                    let b = self[*b].ast;
                    ctx.str("congruence(").pp(&pp_t(m,&a)).str(", ").pp(&pp_t(m,&b)).str(")");
                }
            }
        }
    }

    impl<C:Ctx> pp::Pretty2<C, UndoOp> for Nodes<C> {
        fn pp2_into(&self, m: &C, op: &UndoOp, ctx: &mut pp::Ctx) {
            match op {
                UndoOp::SetOk => { ctx.str("set-ok"); },
                UndoOp::Unmerge{root:a,old_root:b} => {
                    let a = self[a.0].ast;
                    let b = self[b.0].ast;
                    ctx.str("unmerge(").pp(&pp_t(m,&a)).str(", ").pp(&pp_t(m,&b)).str(")");
                },
                UndoOp::RemoveExplLink(a,b) => {
                    let a = self[*a].ast;
                    let b = self[*b].ast;
                    ctx.str("remove-expl-link(").pp(&pp_t(m,&a)).str(", ").pp(&pp_t(m,&b)).str(")");
                },
                UndoOp::UnmapLit(t) => {
                    let t = self[*t].ast;
                    ctx.str("unmap-lit(").pp(&pp_t(m,&t)).str(")");
                },
                UndoOp::RemoveNode(t) => {
                    let t = self[*t].ast;
                    ctx.str("remove-term(").pp(&pp_t(m,&t)).str(")");
                },
            }
        }
    }
}

impl<T:Clone> List<T> {
    /// New list
    #[inline]
    fn new() -> Self {
        List { first: ptr::null_mut(), last: ptr::null_mut(), len: 0 }
    }

    /// Length of the list.
    #[inline(always)]
    fn len(&self) -> usize { self.len as usize }

    /// Iterate over the elements of the list.
    #[inline(always)]
    fn for_each<F>(&self, f: F) where F: FnMut(&T) {
        if self.len > 0 {
            self.for_each_loop(f)
        }
    }

    fn for_each_loop<F>(&self, mut f: F) where F: FnMut(&T) {
        debug_assert!(self.len() > 0);

        let mut ptr = self.first;
        loop {
            let cell = unsafe{ &* ptr };
            f(&cell.0);

            ptr = cell.1;
            if ptr.is_null() {
                break // done
            }
        }
    }

    /// Add `x` into the list.
    fn add(&mut self, alloc: &mut ListAlloc<T>, x: T) {
        // allocate new node
        let ptr = alloc.alloc(ListC(x, self.first));
        self.first = ptr;

        if self.len == 0 {
            // also last element
            self.last = ptr
        }
        self.len += 1;
    }

    /// Remove last added element and return it.
    fn remove(&mut self) -> T {
        debug_assert!(self.len > 0);
        debug_assert!(! self.first.is_null());

        self.len -= 1;
        let ListC(x,next) = unsafe{ self.first.read() };

        if self.len == 0 {
            debug_assert!(next.is_null());
            // list is now empty
            self.first = ptr::null_mut();
            self.last = ptr::null_mut();
        } else {
            // remove first element
            self.first = next;
        }
        x
    }

    /// Append `other` into `self`.
    ///
    /// This modifies `self`, but also possibly `other`.
    fn append(&mut self, other: &mut List<T>) {
        if other.first.is_null() {
            // nothing to do
            debug_assert_eq!(other.len, 0);
        } else if self.first.is_null() {
            // copy other into self
            debug_assert_eq!(self.len, 0);
            self.first = other.first;
            self.last = other.last;
            self.len = other.len;
        } else {
            // make `self.last` point to `other.first`;
            // make `other.first` point to the former `self.last`
            self.len += other.len;

            let n = unsafe{ &mut * self.last };
            debug_assert!(n.1.is_null());
            n.1 = other.first;

            other.first = self.last; // useful when undoing.
            self.last = other.last;
        }
    }

    /// Assuming `self.append(other)` was done earlier, this reverts the operation.
    fn un_append(&mut self, other: &mut List<T>) {
        if other.len == 0 {
            return;
        } else if self.len == other.len {
            // self used to be empty
            self.first = ptr::null_mut();
            self.last = ptr::null_mut();
            self.len = 0;
        } else {
            // `other.first` points to the old `self.last`, so swap them back
            debug_assert!(self.len > other.len);
            self.len -= other.len;

            let last = other.first;
            self.last = last;
            let n = unsafe{ &mut * last };
            other.first = n.1;
            n.1 = ptr::null_mut();
        }
    }
}

impl<F: Eq+Hash+Clone+Debug> Signature<F> {
    /// Create a new signature.
    fn new() -> Self { Signature{ f: None, subs: SVec::new() } }

    /// Clear the signature's content.
    #[inline(always)]
    fn clear(&mut self) {
        self.f = None;
        self.subs.clear()
    }

    /// Compute the signature of `f(args)`.
    fn compute_app<C>(
        &mut self, cc1: &mut CC1<C>, f: &C::Fun, args: &[C::AST]
    ) where C: Ctx<Fun=F> {
        self.clear();
        self.f = Some(f.clone());
        for &u in args {
            self.subs.push(cc1.find_t(u));
        }
    }

    /// Compute the signature of `f(args)`.
    fn compute_app_ho<C>(
        &mut self, cc1: &mut CC1<C>, f: &C::AST, args: &[C::AST]
    ) where C: Ctx {
        self.clear();
        self.subs.push(cc1.find_t(*f));
        for &u in args {
            self.subs.push(cc1.find_t(u));
        }
    }
}
