
//! Congruence closure.
//!
//! The `CC` type is responsible for enforcing congruence and transitivity
//! of equality.

// TODO(perf): backtrackable array allocator for signatures

use {
    std::{ u32, ptr, hash::Hash, fmt::Debug, marker::PhantomData, },
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
pub struct CC<C:Ctx, Th: MicroTheory<C> = ()> {
    n_true: NodeID,
    n_false: NodeID,
    th: Th,
    pending: Vec<NodeID>, // update signatures
    combine: Vec<(NodeID,NodeID,Expl<C::B>)>, // merge
    undo: backtrack::Stack<UndoOp>,
    expl_st: Vec<Expl<C::B>>, // to expand explanations
    tmp_sig: Signature<C::Fun>, // for computing signatures
    traverse: Vec<TraverseTask<C::AST>>, // for adding terms
    sig_tbl: backtrack::HashMap<Signature<C::Fun>, NodeID>,
    lit_expl: backtrack::HashMap<C::B, LitExpl<C::B>>, // pre-explanations for propagations
    cc1: CC1<C>,
}

/// Argument passed to micro theories
pub struct MicroTheoryArg<'a, C:Ctx> {
    pub n_true: NodeID,
    pub n_false: NodeID,
    pub cc1: &'a mut CC1<C>,
    pub combine: &'a mut Vec<(NodeID,NodeID, Expl<C::B>)>,
}

/// A micro-theory, which lives inside the congruence closure
///
/// It works purely by merging classes based on
/// other merges, or by declaring a set of merges inconsistent.
#[allow(unused)]
pub trait MicroTheory<C:Ctx> : backtrack::Backtrackable<C> {
    fn init(m: &mut C) -> Self;

    /// `th.on_new_term(c,t,n)` is called when `t` has been added, with node `n`
    fn on_new_term(&mut self, c: &mut C, cc1: &mut CC1<C>, t: &C::AST, n: NodeID) {}

    /// Called before the merge of `a` and `b`
    fn before_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, a: NodeID, b: NodeID) {}

    /// Called after the merge of `a` and `b`
    fn after_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, a: NodeID, b: NodeID) {}

    /// Called with all terms whose signature is to be updated
    fn on_sig_update(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, t: &C::AST, n: NodeID) {}
}

/// Implement `MicroTheory` for a tuple of types themselves micro-theories.
macro_rules! impl_micro_theory_tuple {
    () => ();
    ( $( $t: ident ,)+ ) => {
        #[allow(non_snake_case)]
        impl<C:Ctx, $( $t ,)* > MicroTheory<C> for ( $( $t ,)* )
            where $( $t : MicroTheory<C> ),*
        {
            fn init(m: &mut C) -> Self {
                ($( $t::init(m) ,)* )
            }

            fn on_new_term(&mut self, c: &mut C, cc1: &mut CC1<C>, t: &C::AST, n: NodeID) {
                let ($( $t ,)*) = self;
                $(
                    $t.on_new_term(c, cc1, t, n);
                )*
            }

            /// Called before the merge of `a` and `b`
            fn before_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, a: NodeID, b: NodeID)
            {
                let ($( $t ,)*) = self;
                $( $t.before_merge(c, acts, a, b); )*
            }

            /// Called after the merge of `a` and `b`
            fn after_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, a: NodeID, b: NodeID)
            {
                let ($( $t ,)*) = self;
                $( $t.after_merge(c, acts, a, b); )*
            }

            /// Called with all terms whose signature is to be updated
            fn on_sig_update(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, t: &C::AST, n: NodeID)
            {
                let ($( $t ,)*) = self;
                $( $t.on_sig_update(c, acts, t, n); )*
            }
        }

        impl_micro_theory_tuple_peel!{ $($t,)* }
    };
}

// recursion
macro_rules! impl_micro_theory_tuple_peel {
    ( $t0: ident, $( $t: ident,)* ) => { impl_micro_theory_tuple! { $( $t ,)* } }
}
impl_micro_theory_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, }

impl<C:Ctx> MicroTheory<C> for () {
    fn init(_m: &mut C) -> Self { () }
}

/// internal state, with just the core structure for nodes and parent sets
pub struct CC1<C:Ctx> {
    ok: bool, // no conflict?
    propagate: bool, // do we propagate?
    alloc_parent_list: ListAlloc<NodeID>,
    alloc_lit_list: ListAlloc<(NodeID,C::B)>,
    nodes: Nodes<C>,
    confl: Vec<C::B>, // local for conflict
    tmp_expl: Vec<NodeID>,
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
pub struct NodeID(u32);

/// Map terms into the corresponding node.
struct Nodes<C:Ctx>{
    n_true: NodeID,
    n_false: NodeID,
    map: FxHashMap<C::AST, NodeID>,
    nodes: Vec<Node<C>>,
    find_stack: Vec<NodeID>,
}

#[allow(type_alias_bounds)]
pub type Node<C:Ctx> = NodeDef<C::AST, C::B>;

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
pub struct NodeDef<AST, B> where AST : Sized, B : Sized {
    pub id: NodeID,
    pub ast: AST, // what AST does this correspond to?
    next: NodeID, // next elt in class
    expl: Option<(NodeID, Expl<B>)>, // proof forest //TODO: use allocator?
    as_lit: List<(NodeID,B)>, // for repr, list of literals in the class
    root: NodeID, // current representative (initially, itself)
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

/// An explanation for a merge
#[derive(Clone,Debug)]
pub enum Expl<B> {
    Axiom, // trivial explanation
    Lit(B), // because literal was asserted
    Congruence(NodeID, NodeID), // because terms are congruent
    AreEq(NodeID, NodeID), // because terms are equal
    Conj(Vec<Expl<B>>), // conjunction of explanations
}

/// Undo operations on the congruence closure
#[derive(Debug)]
enum UndoOp {
    SetOk,
    RemoveNode(NodeID),
    UnmapLit(NodeID),
    Unmerge {
        root: NodeID, // the new repr
        old_root: NodeID, // merged into `a`
    }, // unmerge these two reprs
    RemoveExplLink(NodeID,NodeID), // remove explanation link connecting these
}

/// A signature for a term, obtained by replacing its subterms with their repr.
///
/// Signatures have the properties that if two terms are congruent,
/// then their signatures are identical.
#[derive(Eq,PartialEq,Hash,Clone,Debug)]
pub struct Signature<F> {
    f: Option<F>,
    subs: SVec<NodeID>
}

// implement main interface
impl<C:Ctx, Th: MicroTheory<C>> CCInterface<C> for CC<C, Th> {
    fn merge(&mut self, m: &mut C, t1: C::AST, t2: C::AST, lit: C::B) {
        debug!("merge {} and {} (expl {:?})", pp_t(m,&t1), pp_t(m,&t2), lit);
        // FIXME debug!("merge {} and {} (expl {:?})", pp_term(m,&t1), pp_term(m,&t2), lit);
        let n1 = self.add_term(m, t1);
        let n2 = self.add_term(m, t2);
        let expl = Expl::Lit(lit);
        self.combine.push((n1,n2,expl));
    }

    fn distinct(&mut self, _m: &mut C, _ts: &[C::AST], _lit: C::B) {
        unimplemented!("distinct is not supported yet")
        /*
        let mut v = SVec::with_capacity(ts.len());
        v.extend_from_slice(ts);
        let expl = Expl::Lit(lit);
        self.tasks.push_back(Task::Distinct(v,expl))
        */
    }

    fn add_literal(&mut self, m: &mut C, t: C::AST, lit: C::B) {
        let n = self.add_term(m, t);
        self.map_to_lit(m, n, lit);
    }

    #[inline]
    fn final_check<A>(&mut self, m: &mut C, acts: &mut A)
        where A: Actions<C>
    {
        self.check_internal(m, acts)
    }

    #[inline]
    fn partial_check<A>(&mut self, m: &mut C, acts: &mut A)
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

    fn enable_propagation(&mut self, b: bool) { self.cc1.propagate = b; }

    fn impl_descr() -> &'static str { "fast congruence closure"}
}

impl<C:Ctx, Th: MicroTheory<C>> CC<C, Th> {
    // main `check` function, performs the fixpoint
    fn check_internal<A>(&mut self, m: &mut C, acts: &mut A)
        where A: Actions<C>
    {
        debug!("check-internal (pending: {}, combine: {})",
            self.pending.len(), self.combine.len());
        self.fixpoint(m, Some(acts));
        if ! self.cc1.ok {
            debug_assert!(self.cc1.confl.len() >= 1); // must have some conflict
            let costly = true;
            acts.raise_conflict(&self.cc1.confl, costly)
        }
    }

    /// Main CC algorithm.
    fn fixpoint(&mut self, m: &mut C, mut acts: Option<&mut dyn Actions<C>>) {
        let CC{
            combine,cc1,pending,th,expl_st,undo,tmp_sig,
            sig_tbl,lit_expl,n_true,n_false,..} = self;
        let mut combine2 = vec!();
        loop {
            if !cc1.ok {
                combine.clear();
                pending.clear();
                break
            }

            {
                let mut updsig =
                    UpdateSigPhase{cc1,combine,sig_tbl,tmp_sig,
                    n_true: *n_true,n_false: *n_false};
                for &t in pending.iter() {
                    if updsig.cc1[t].needs_sig() {
                        updsig.update_signature(m, th, t);
                    }
                }
                pending.clear();
            }

            {
                let mut merger = MergePhase{
                    cc1,pending,expl_st,undo,lit_expl, acts: &mut acts,
                    combine2: &mut combine2,
                    n_true: *n_true,n_false: *n_false};
                while combine.len() > 0 {
                    for (t,u,expl) in combine.iter() {
                        merger.merge(m,th,*t,*u,expl.clone())
                    }
                    combine.clear();
                    // micro theories may have more things to propagate
                    combine.extend_from_slice(merger.combine2);
                    merger.combine2.clear();
                }
            }

            if pending.is_empty() {
                break; // done
            }
        }
    }
}

// main congruence closure operations
impl<C:Ctx, Th:MicroTheory<C>> CC<C, Th> {
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
        let th = Th::init(m);
        CC{
            n_true, n_false,
            th,
            pending: vec!(),
            combine: vec!(),
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
    fn add_term(&mut self, m: &mut C, t0: C::AST) -> NodeID {
        match self.cc1.nodes.map.get(&t0) {
            Some(n) => *n,
            None => self.add_term_rec(m, t0),
        }
    }

    fn add_term_rec(&mut self, m: &mut C, t0: C::AST) -> NodeID {
        self.traverse.clear();

        let CC {traverse, undo, cc1, pending, th, ..} = self;
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
                        let ur = cc1.find_t(u);
                        let parents = cc1.nodes.parents_mut(ur);
                        parents.add(&mut cc1.alloc_parent_list, n);
                    });
                    // remove `t` before its children
                    undo.push_if_nonzero(UndoOp::RemoveNode(n));

                    if view.needs_sig() {
                        cc1.nodes[n].set_needs_sig();
                        pending.push(n);
                    }

                    th.on_new_term(m, cc1, &t, n);
                },
            }
        }
        assert!(n0.is_some());
        n0.unwrap()
    }

    fn map_to_lit(&mut self, m: &C, t: NodeID, lit: C::B) {
        if ! self.cc1.ok { return; }

        // add to literal
        let tr = self.cc1.find(t);
        let CC1{nodes, alloc_lit_list, ..} = &mut self.cc1;
        let n = &mut nodes[tr];
        if n.as_lit.iter().all(|(_,lit2)| *lit2 != lit) {
            n.as_lit.add(alloc_lit_list, (t,lit));
            self.undo.push_if_nonzero(UndoOp::UnmapLit(t));
            debug!("map term {} to literal {:?}", pp::pp2(self,m,&t), lit);
        }
    }
}

/// Internal structure used during merging of newly equivalent classes.
pub struct MergePhase<'a,'b:'a, C:Ctx> {
    pub(crate) cc1: &'a mut CC1<C>,
    pub(crate) n_true: NodeID,
    pub(crate) n_false: NodeID,
    pub(crate) pending: &'a mut Vec<NodeID>,
    pub(crate) combine2: &'a mut Vec<(NodeID, NodeID, Expl<C::B>)>, // temporary
    pub(crate) expl_st: &'a mut Vec<Expl<C::B>>,
    undo: &'a mut backtrack::Stack<UndoOp>,
    acts: &'a mut Option<&'b mut dyn Actions<C>>,
    lit_expl: &'a mut backtrack::HashMap<C::B, LitExpl<C::B>>, // pre-explanations for propagations
}

/// Internal structure used during update of term signatures.
pub struct UpdateSigPhase<'a,C:Ctx> {
    pub(crate) cc1: &'a mut CC1<C>,
    pub(crate) n_true: NodeID,
    pub(crate) n_false: NodeID,
    pub(crate) combine: &'a mut Vec<(NodeID,NodeID,Expl<C::B>)>,
    pub(crate) sig_tbl: &'a mut backtrack::HashMap<Signature<C::Fun>, NodeID>,
    pub(crate) tmp_sig: &'a mut Signature<C::Fun>,
}

// FIXME: when merging `a` and `b`, need to call micro-theory `on_signature`
// on parents of both a and b (not just b)

impl<'a, 'b:'a, C:Ctx> MergePhase<'a,'b,C> {
    /// Merge `a` and `b`, if they're not already equal.
    fn merge<Th:MicroTheory<C>>(
        &mut self, m: &mut C, th: &mut Th,
        mut a: NodeID, mut b: NodeID, expl: Expl<C::B>
    ) {
        let mut ra = self.cc1.nodes.find(a);
        let mut rb = self.cc1.nodes.find(b);
        debug_assert!(self.cc1.is_root(ra), "{}.repr = {}",
            pp::pp2(self.cc1,m,&a), pp::pp2(self.cc1,m,&ra));
        debug_assert!(self.cc1.is_root(rb), "{}.repr = {}",
            pp::pp2(self.cc1,m,&b), pp::pp2(self.cc1,m,&rb));
        // debug_assert!(self.cc1.is_root(ra.0), "{}.repr = {}", pp_term(m,&a), pp_term(m,&ra.0));
        // debug_assert!(self.cc1.is_root(rb.0), "{}.repr = {}", pp_term(m,&b), pp_term(m,&rb.0));

        if ra == rb {
            return; // done already
        }

        // access the two nodes
        let (na, nb) = self.cc1.nodes.get2(ra, rb);

        // NOTE: would be nice to put `unlikely` there once it stabilizes
        if na.len() + nb.len() > u32::MAX as usize {
            panic!("too many terms in one class")
        }

        // merge smaller one into bigger one, except that booleans are
        // always representatives
        if rb == self.n_true || rb == self.n_false {
            // conflict: merge true with false (since they are distinct)
            if ra == self.n_true || ra == self.n_false {
                // generate conflict from `expl`, `a == ra`, `b == rb`
                trace!("generate conflict from merge of true/false from {} and {}",
                       pp::pp2(self.cc1,m,&a), pp::pp2(self.cc1,m,&b));
                assert_ne!(ra, rb);
                self.cc1.ok = false;
                self.undo.push_if_nonzero(UndoOp::SetOk);
                {
                    let mut er = ExplResolve::new(&mut self.cc1, &mut self.expl_st);
                    er.add_expl(expl);
                    er.explain_eq(m, a, ra);
                    er.explain_eq(m, b, rb);
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
        } else if ra == self.n_true || ra == self.n_false {
            // `ra` must be repr
        } else if na.len() < nb.len() {
            // swap a and b
            std::mem::swap(&mut ra, &mut rb);
            std::mem::swap(&mut a, &mut b);
        }
        drop(na);
        drop(nb);

        trace!("merge {} into {}", pp::pp2(self.cc1,m,&rb), pp::pp2(self.cc1,m,&ra));

        // call micro theories
        {
            let mut acts = MicroTheoryArg{
                cc1: &mut self.cc1, n_true: self.n_true, n_false: self.n_false,
                combine: &mut self.combine2};
            th.before_merge(m, &mut acts, a, b);
        }

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

        let MergePhase{cc1, acts, lit_expl, n_true, n_false, combine2, ..} = self;

        // if ra is {true,false}, propagate lits
        if cc1.propagate && acts.is_some() &&
            (ra == cc1.nodes.n_true || ra == cc1.nodes.n_false) {
            trace!("{}.class: look for propagations", pp::pp2(*cc1,m,&rb));
            let acts = &mut (match acts { Some(a) => a, None => unreachable!() });
            for (n_id, mut lit) in cc1[rb].as_lit.iter() {
                let n = &cc1[*n_id];
                // if a=true/false, and `n` has a literal, propagate the literal
                // assuming it's not known to be true already.
                if !lit_expl.contains_key(&lit) {
                    // future expl: `n=b=a=ra` (where ra∈{true,false})
                    let e = LitExpl::Propagated {
                        expl: expl.clone(),
                        eqns: [(n.id, b), (a, ra)],
                    };
                    if ra == *n_true {
                        trace!("propagate literal {:?} (for true≡{}, {:?})",
                            lit, pp_t(m,&n.ast), &expl);
                        acts.propagate(lit);
                    } else {
                        debug_assert_eq!(ra, *n_false);
                        lit = !lit;
                        trace!("propagate literal {:?} (for false≡{}, {:?})",
                            lit, pp_t(m,&n.ast), &expl);
                        acts.propagate(lit);
                    }
                    lit_expl.insert(lit, e);
                }
            }
        }

        // set `rb.root` to `ra`
        cc1[rb].root = ra;

        // ye ole' switcharoo (of doubly linked lists for the equiv class)
        //
        // instead of:  a --> next_a,  b --> next_b
        // have:  a --> next_b, b --> next_a
        //
        {
            // access the two nodes, again
            let (na, nb) = cc1.nodes.get2(ra, rb);

            let next_a = na.next;
            let next_b = nb.next;

            na.next = next_b;
            nb.next = next_a;

            // also merge parent/lit lists
            na.parents.append(&mut nb.parents);
            na.as_lit.append(&mut nb.as_lit);
        }

        // call micro theories
        {
            let mut acts = MicroTheoryArg{
                cc1, n_true: *n_true, n_false: *n_false,
                combine: combine2};
            th.after_merge(m, &mut acts, a, b);
        }
    }
}

impl<'a, C:Ctx> UpdateSigPhase<'a,C> {
    /// Check and update signature of `t`, possibly adding new merged by congruence.
    fn update_signature<Th:MicroTheory<C>>(&mut self, m: &mut C, th: &mut Th, n: NodeID) {
        let UpdateSigPhase{
            tmp_sig: ref mut sig, cc1, sig_tbl, combine, n_true, n_false, ..} = self;
        let t = cc1[n].ast;
        let has_sig =
            m.is_app(&t) // shortcut &&
            &&
            match m.view_as_cc_term(&t) {
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
        // call micro theories
        {
            let mut arg = MicroTheoryArg{
                cc1, n_true: *n_true, n_false: *n_false, combine,
            };
            th.on_sig_update(m, &mut arg, &t, n);
        }
    }
}

// query the graph
impl<C:Ctx> CC1<C> {
    fn new() -> Self {
        CC1 {
            nodes: Nodes::new(),
            propagate: true,
            ok: true,
            alloc_parent_list: backtrack::Alloc::new(),
            alloc_lit_list: backtrack::Alloc::new(),
            tmp_expl: vec!(),
            confl: vec!(),
        }
    }

    #[inline(always)]
    pub(crate) fn find(&mut self, t: NodeID) -> NodeID { self.nodes.find(t) }

    #[inline(always)]
    pub(crate) fn find_t(&mut self, t: &C::AST) -> NodeID { self.nodes.find_t(t) }

    #[inline(always)]
    pub(crate) fn is_root(&mut self, id: NodeID) -> bool { self.find(id) == id }

    #[inline(always)]
    pub(crate) fn is_eq(&mut self, a: NodeID, b: NodeID) -> bool {
        self.nodes.is_eq(a,b)
    }

    /// Find the ID of the given term.
    #[inline]
    pub(crate) fn get_term_id(&self, t: &C::AST) -> NodeID {
        self.nodes.get_term_id(t)
    }

    /// Undo one change.
    fn perform_undo(&mut self, m: &C, op: UndoOp) {
        trace!("perform-undo {}", pp::pp2(&self.nodes,m,&op));
        match op {
            UndoOp::SetOk => {
                self.ok = true;
                self.confl.clear();
            },
            UndoOp::Unmerge {root: a, old_root: b} => {
                assert_ne!(a,b); // crucial invariant

                let (na, nb) = self.nodes.get2(a, b);

                // inverse switcharoo for the class linked lists
                {
                    let next_a = na.next;
                    let next_b = nb.next;

                    na.next = next_b;
                    nb.next = next_a;

                    na.parents.un_append(&mut nb.parents);
                    na.as_lit.un_append(&mut nb.as_lit);
                }

                // reset `root` pointer for `nb`
                // reset root for the classes of terms that are now repr again,
                // if they haven't been removed.
                self.nodes.iter_class_mut(b, |nb1| {
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
                    let ur = self.find_t(u);
                    let parents = self.nodes.parents_mut(ur);
                    let _n = parents.remove();
                    debug_assert_eq!(_n, n);
                });
            }
            UndoOp::UnmapLit(t) => {
                // pop last
                let tr = self.find(t);
                let n = &mut self[tr];
                debug_assert!(n.as_lit.len() > 0);
                let (_t2,_) = n.as_lit.remove();
                assert_eq!(_t2, t);
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

    /// Find the closest common ancestor of `a` and `b` in the proof
    /// forest.
    /// Precond: `is_eq(a,b)`.
    fn find_expl_common_ancestor(&mut self, a0: NodeID, b0: NodeID) -> NodeID {
        debug_assert!(self.nodes.is_eq(a0,b0));
        let CC1{tmp_expl: to_clean, nodes, ..} = self;

        to_clean.clear();

        // walk in lockstep, until we reached a node already marked
        //
        // invariants:
        // I1: `a.marked() ==> a.expl.is_some()`
        // I2: `a.marked() ==> to_clean.contains(a)`
        let res = {
            let mut a = a0;
            let mut b = b0;

            loop {
                if a==b { break a }

                // if `a` is marked, it means it's on both path, so it must
                // be the first common ancestor.
                // I1 prevents the root from being returned here.
                if nodes[a].marked() { break a }
                if nodes[b].marked() { break b }

                if let Some((a2,_)) = nodes[a].expl {
                    nodes[a].mark();
                    to_clean.push(a);
                    a = a2;
                }
                if let Some((b2,_)) = nodes[b].expl {
                    nodes[b].mark();
                    to_clean.push(b);
                    b = b2;
                }
            }
        };

        // cleanup (see I2)
        for &a in to_clean.iter() {
            nodes[a].unmark()
        }

        res
    }
}

impl<C:Ctx, Th: MicroTheory<C>> backtrack::Backtrackable<C> for CC<C, Th> {
    fn push_level(&mut self, m: &mut C) {
        trace!("push-level");
        self.fixpoint(m, None); // be sure to commit changes before saving
        self.undo.push_level();
        self.sig_tbl.push_level();
        self.cc1.alloc_parent_list.push_level();
        self.cc1.alloc_lit_list.push_level();
        self.lit_expl.push_level();
        self.th.push_level(m);
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
            cc1.alloc_lit_list.pop_levels(n);
            self.lit_expl.pop_levels(n);
            self.th.pop_levels(m, n);

            self.pending.clear();
            self.combine.clear();
        }
    }
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

    #[inline]
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
                Expl::Axiom => (), // nothing to do
                Expl::Lit(lit) => {
                    self.cc1.confl.push(lit);
                },
                Expl::AreEq(a,b) => {
                    self.explain_eq(m, a, b);
                },
                Expl::Conj(v) => {
                    // explain each element of the conjunction
                    self.expl_st.extend(v.iter().cloned());
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
        // NOTE: remove? self.cc1.confl.sort_unstable();
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
    pub(crate) fn contains(&self, t: &C::AST) -> bool { self.map.contains_key(t) }

    /// Find the ID of the given term.
    #[inline]
    pub(crate) fn get_term_id(&self, t: &C::AST) -> NodeID {
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
    pub(crate) fn find_t(&mut self, t: &C::AST) -> NodeID {
        let n = self.get_term_id(t);
        self.find(n)
    }

    /// Find representative of the given node
    #[inline(always)]
    pub(crate) fn find(&mut self, t: NodeID) -> NodeID {
        let root = self[t].root;

        if root == t {
            root // fast path
        } else {
            let root = self.find_rec(root, 16); // use recursion
            self[t].root = root; // update this pointer
            root
        }
    }

    // find + path compression, using recursion up to `limit`
    fn find_rec(&mut self, t: NodeID, limit: usize) -> NodeID {
        let root = self[t].root;
        if root == t {
            root
        } else {
            // recurse
            let root = {
                if limit == 0 {
                    self.find_loop(root)
                } else {
                    self.find_rec(root, limit-1)
                }
            };
            self[t].root = root;
            root
        }
    }

    // find + path compression, using a loop
    fn find_loop(&mut self, mut t: NodeID) -> NodeID {
        debug_assert_eq!(self.find_stack.len(), 0);

        let root = loop {
            let root = self[t].root;
            if t == root {
                break root
            } else {
                // seek further
                self.find_stack.push(t);
                t = root
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
    pub(crate) fn is_eq(&mut self, a: NodeID, b: NodeID) -> bool {
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
    pub(crate) fn iter_class_mut<F>(&mut self, r: NodeID, mut f: F)
        where F: for<'b> FnMut(&'b mut Node<C>)
    {
        let mut t = r;
        loop {
            let n = &mut self[t];
            f(n);

            t = n.next;
            if t == r { break } // done the full loop
        }
    }

    /// Call `f` on all parents of all nodes of the class of `r`
    #[inline]
    pub(crate) fn iter_parents<F>(&mut self, r: NodeID, mut f: F)
        where F: FnMut(&NodeID)
    {
        debug_assert_eq!(r, self.find(r), "must be root");
        for x in self[r].parents.iter() { f(x); }
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

    impl<C:Ctx, Th: MicroTheory<C>> pp::Pretty2<C, NodeID> for CC<C, Th> {
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
    const FLG_MARKED : u8 = 0b10;

    impl<AST, B:Clone> NodeDef<AST, B> {
        /// Create a new node with the given ID and AST.
        pub fn new(ast: AST, id: NodeID) -> Self {
            let parents = List::new();
            NodeDef {
                id, ast, next: id, expl: None,
                root: id, as_lit: List::new(), parents, flags: 0,
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

        #[inline(always)]
        pub fn marked(&self) -> bool { (self.flags & FLG_MARKED) != 0 }

        #[inline(always)]
        pub fn mark(&mut self) { self.flags |= FLG_MARKED }

        #[inline(always)]
        pub fn unmark(&mut self) { self.flags &= !FLG_MARKED }
    }
}

mod expl {
    use super::*;

    impl<C:Ctx> pp::Pretty2<C, Expl<C::B>> for Nodes<C> {
        fn pp2_into(&self, m: &C, expl: &Expl<C::B>, ctx: &mut pp::Ctx) {
            match expl {
                Expl::Axiom => { ctx.str("axiom"); },
                Expl::Lit(lit) => {
                    ctx.str("lit(").debug(lit).str(")");
                },
                Expl::AreEq(a,b) => {
                    let a = self[*a].ast;
                    let b = self[*b].ast;
                    ctx.str("are-eq(").pp(&pp_t(m,&a)).str(", ").pp(&pp_t(m,&b)).str(")");
                }
                Expl::Conj(v) => {
                    ctx.sexp(|ctx| {
                        for e in v.iter() { self.pp2_into(m, e, ctx) }
                    });
                },
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
                    let a = self[*a].ast;
                    let b = self[*b].ast;
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

    /// Iterate over the list's elements.
    fn iter(&self) -> impl Iterator<Item=&T> {
        ListIter(self.first, PhantomData)
    }
}

struct ListIter<'a, T: 'a>(*mut ListC<T>, PhantomData<&'a T>);

impl<'a, T> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_null() {
            None
        } else {
            let c = unsafe { &*self.0 };
            let x = &c.0;
            *self = ListIter(c.1, PhantomData);
            Some(x)
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
        for u in args {
            self.subs.push(cc1.find_t(u));
        }
    }

    /// Compute the signature of `f(args)`.
    fn compute_app_ho<C>(
        &mut self, cc1: &mut CC1<C>, f: &C::AST, args: &[C::AST]
    ) where C: Ctx {
        self.clear();
        self.subs.push(cc1.find_t(f));
        for u in args {
            self.subs.push(cc1.find_t(u));
        }
    }
}
