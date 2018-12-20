
//! Congruence closure.
//!
//! The `CC` type is responsible for enforcing congruence and transitivity
//! of equality.

// TODO: parametrize by "micro theories" (which just work on merges + expl)

// micro theories:
// - rule for `not` (t == true |- not t == false, and conversely)
// - rule for `ite` (t == true |- not t == false, and conversely)

use {
    std::{
        //ops::{Deref,DerefMut},
        u32, marker::PhantomData,
        collections::VecDeque,
    },
    batsmt_core::{ast::{self,AST,View},Symbol,backtrack},
    batsmt_pretty as pp,
    fxhash::FxHashMap,
    crate::{types::BoolLit,PropagationSet,Conflict,Builtins,CCInterface,SVec},
};

type M<S> = ast::Manager<S>;

/// The congruence closure
pub struct CC<S:Symbol,B:BoolLit> {
    m_s: PhantomData<S>,
    cc0: CC0<S,B>,
}

/// internal state of the congruence closure
struct CC0<S:Symbol,B:BoolLit> {
    b: Builtins,
    m: ast::Manager<S>, // the AST manager
    tasks: VecDeque<Task<B>>, // operations to perform
    undo: backtrack::Stack<UndoOp>,
    tmp_parents: ParentList,
    confl: Vec<B>, // local for conflict
    props: PropagationSet<B>, // local for propagations
    traverse: ast::iter_suffix::State<S>, // for recursive traversal
    expl_st: Vec<Expl<B>>, // to expand explanations
    tmp_sig: Signature, // for computing signatures
    sig_tbl: backtrack::HashMap<Signature, AST>,
    cc1: CC1<S,B>,
}

/// internal state
struct CC1<S:Symbol,B:BoolLit> {
    m: ast::Manager<S>, // the AST manager
    ok: bool, // no conflict?
    nodes: ast::DenseMap<Node<B>>,
    parents: FxHashMap<Repr, ParentList>, // parents of the given class
}

/// One node in the congruence closure's E-graph.
///
/// It contains:
/// - the term itself
/// - a direct pointer to the class' root
/// - double-linked list pointers for iterating the class, along with the class' size
/// - the proof forest pointer
/// - an optional mapping from the term to a boolean literal (for propagation)
#[derive(Clone)]
struct Node<B:BoolLit> {
    id: NodeID,
    next: NodeID, // next elt in class
    prev: NodeID, // previous elt in class
    size: u32, // number of elements in class
    expl: Option<(NodeID, Expl<B>)>, // proof forest
    as_lit: Option<B>, // if this term corresponds to a boolean literal
    root: Repr, // current representative (initially, itself)
}

#[derive(Clone)]
struct ParentList(SVec<NodeID>);

/// The name for a node.
///
/// For now it's just the AST this node corresponds to.
type NodeID = AST;

/// A representative
#[derive(Debug,Clone,Copy,Eq,PartialEq,Hash,Ord,PartialOrd)]
struct Repr(NodeID);

/// An explanation for a merge
#[derive(Clone,Debug)]
enum Expl<B> {
    Lit(B), // because literal was asserted
    Congruence(AST,AST), // because terms are congruent
    AreEq(AST,AST), // because terms are equal
}

/// Undo operations on the congruence closure
#[derive(Debug)]
enum UndoOp {
    SetOk,
    RemoveTerm(AST),
    UnmapLit(AST),
    Unmerge {
        a: Repr, // the new repr
        b: Repr, // merged into `a`
    }, // unmerge these two reprs
}

/// Operation to perform in the main fixpoint
#[derive(Debug)]
enum Task<B> {
    AddTerm(AST), // add term if not present
    MapToLit(AST,B), // map term to lit
    UpdateSig(AST), // re-check signature
    Merge(AST, AST, Expl<B>), // merge the classes of these two terms
    Distinct(SVec<AST>, Expl<B>),
}

/// A signature for a term, obtained by replacing its subterms with their repr.
///
/// Signatures have the properties that if two terms are congruent,
/// then their signatures are identical.
#[derive(Eq,PartialEq,Hash,Clone,Debug)]
struct Signature(SVec<Repr>);

// implement main interface
impl<S:Symbol, B:BoolLit> CCInterface<B> for CC<S,B> {
    fn merge(&mut self, t1: AST, t2: AST, lit: B) {
        let expl = Expl::Lit(lit);
        self.cc0.tasks.push_back(Task::AddTerm(t1));
        self.cc0.tasks.push_back(Task::AddTerm(t2));
        self.cc0.tasks.push_back(Task::Merge(t1,t2,expl))
    }

    fn distinct(&mut self, ts: &[AST], lit: B) {
        let mut v = SVec::with_capacity(ts.len());
        v.extend_from_slice(ts);
        let expl = Expl::Lit(lit);
        self.cc0.tasks.push_back(Task::Distinct(v,expl))
    }

    fn final_check(&mut self) -> Result<&PropagationSet<B>, Conflict<B>> {
        debug!("cc.final-check()");
        self.check_internal()
    }

    fn partial_check(&mut self) -> Option<Result<&PropagationSet<B>, Conflict<B>>> {
        debug!("cc.partial-check()");
        Some(self.check_internal())
    }

    // FIXME
    // fn has_partial_check() -> bool { true }
    fn has_partial_check() -> bool { false }

    fn add_literal(&mut self, t: AST, lit: B) {
        self.cc0.tasks.push_back(Task::AddTerm(t));
        self.cc0.tasks.push_back(Task::MapToLit(t, lit));
    }

    fn impl_descr(&self) -> &'static str { "fast congruence closure"}
}

// main API
impl<S, B:BoolLit> CC<S, B> where S: Symbol {
    /// Create a new congruence closure using the given `Manager`
    pub fn new(m: &ast::Manager<S>, b: Builtins) -> Self {
        CC {
            m_s: PhantomData::default(),
            cc0: CC0::new(m, b),
        }
    }
}

impl<S:Symbol, B: BoolLit> CC<S, B> {
    // main `check` function, performs the fixpoint
    fn check_internal(&mut self) -> Result<&PropagationSet<B>, Conflict<B>> {
        debug!("check-internal ({} tasks)", self.cc0.tasks.len());
        while let Some(task) = self.cc0.tasks.pop_front() {
            if ! self.cc0.cc1.ok {
                debug_assert!(self.cc0.confl.len() >= 1); // must have some conflict
                return Err(Conflict(&self.cc0.confl))
            }
            match task {
                Task::AddTerm(t) => self.cc0.add_term(t),
                Task::UpdateSig(t) => self.cc0.update_signature(t),
                Task::Merge(a,b,expl) => self.cc0.merge(a, b, expl),
                Task::MapToLit(t,lit) => self.cc0.map_to_lit(t, lit),
                Task::Distinct(..) => {
                    unimplemented!("cannot handle distinct yet")
                },
            }
        }
        if self.cc0.cc1.ok {
            Ok(&self.cc0.props)
        } else {
            Err(Conflict(&self.cc0.confl))
        }
    }
}

/// Does `t` need to be entered in the signature table?
fn needs_signature<S:Symbol>(m: &M<S>, t: AST) -> bool {
    match m.get().view(t) {
        View::Const(_) => false,
        View::App{..} => true,
    }
}

// main congruence closure operations
impl<S:Symbol, B: BoolLit> CC0<S,B> {
    /// Create a core congruence closure
    fn new(m: &M<S>, b: Builtins) -> Self {
        let mut cc1 = CC1::new(m);
        // add builtins
        cc1.nodes.insert(b.true_, Node::new(b.true_));
        cc1.parents.insert(Repr(b.true_), ParentList::new());
        cc1.nodes.insert(b.false_, Node::new(b.false_));
        cc1.parents.insert(Repr(b.false_), ParentList::new());
        CC0{
            b, m: m.clone(),
            tasks: VecDeque::new(),
            confl: vec!(),
            props: PropagationSet::new(),
            undo: backtrack::Stack::new(),
            tmp_parents: ParentList::new(),
            traverse: ast::iter_suffix::State::new(m),
            tmp_sig: Signature::new(),
            sig_tbl: backtrack::HashMap::new(),
            expl_st: vec!(),
            cc1,
        }
    }

    fn find(&self, id: NodeID) -> Repr { self.cc1.find(id) }
    fn is_root(&self, id: NodeID) -> bool { self.find(id).0 == id }

    /// Add this term to the congruence closure, if not present already.
    fn add_term(&mut self, t0: AST) {
        if self.cc1.nodes.contains(t0) {
            return; // fast path: already there
        }

        self.traverse.clear();

        let CC0 {traverse, undo, m, cc1, tasks, ..} = self;
        let mr = m.get();
        // traverse in postfix order (shared context: `cc1`)
        traverse.iter(
            t0, cc1,
            |cc1,t| {
                let enter = !cc1.nodes.contains(t);
                if enter {
                    // avoid entering twice
                    cc1.nodes.insert(t, Node::new(t));
                }
                enter
            },
            |cc1,t| {
                debug_assert!(cc1.nodes.contains(t));
                trace!("add-term {}", m.pp(t));
                cc1.nodes.insert(t, Node::new(t));
                let old_par = cc1.parents.insert(Repr(t), ParentList::new());
                debug_assert!(old_par.is_none());

                // now add itself to its children's list of parents.
                for u in mr.view(t).subterms() {
                    debug_assert!(cc1.nodes.contains(u)); // postfix order
                    let parents = cc1.parents_mut(cc1.find(u));
                    parents.push(t);
                }
                // remove `t` before its children
                undo.push_if_nonzero(UndoOp::RemoveTerm(t));

                if needs_signature(m, t) {
                    tasks.push_back(Task::UpdateSig(t));
                }
            });
    }

    fn map_to_lit(&mut self, t: AST, lit: B) {
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
    fn merge(&mut self, a: AST, b: AST, expl: Expl<B>) {
        debug_assert!(self.cc1.contains_ast(a));
        debug_assert!(self.cc1.contains_ast(b));

        let mut ra = self.cc1.find(a);
        let mut rb = self.cc1.find(b);
        debug_assert!(self.is_root(ra.0), "{}.repr = {}", self.m.pp(a), self.m.pp(ra.0));
        debug_assert!(self.is_root(rb.0), "{}.repr = {}", self.m.pp(b), self.m.pp(rb.0));

        if ra == rb {
            return; // done already
        }

        let Node {prev: prev_a, next: next_a, size: size_a, ..} = self.cc1[ra.0];
        let Node {prev: prev_b, next: next_b, size: size_b, ..} = self.cc1[rb.0];

        if (size_a as usize) + (size_b as usize) > u32::MAX as usize {
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
                self.confl.clear();
                self.expl_st.clear();
                self.expl_st.push(expl);
                self.explain_eq(a, ra.0);
                self.explain_eq(b, rb.0);
                self.expl_fixpoint();
                // cleanup conflict
                self.confl.sort_unstable();
                self.confl.dedup();
                trace!("computed conflict: {:?}", &self.confl);
                return;
            }
            std::mem::swap(&mut ra, &mut rb);
        } else if ra.0 == self.b.true_ || ra.0 == self.b.false_ {
            // `ra` must be repr
        } else if size_a < size_b {
            std::mem::swap(&mut ra, &mut rb);
        }

        trace!("merge {}.repr into {}", self.m.pp(rb.0), self.m.pp(ra.0));

        // update explanation
        self.cc1.reroot_forest(rb.0);
        self.cc1[rb.0].expl = Some((ra.0, expl));

        // local copy of parents(b).
        // NOTE: we know they're not aliased, we could use a pointer?
        {
            self.tmp_parents.clear();
            let parents_b = &self.cc1.parents(rb);
            self.tmp_parents.append(parents_b);

            // might need to check for congruence again for parents of `b`,
            // since one of their direct child (b) now has a different
            // representative
            for &p_b in parents_b.iter() {
                if needs_signature(&self.m, p_b) {
                    self.tasks.push_back(Task::UpdateSig(p_b));
                }
            }
        }

        let parents_a = self.cc1.parents_mut(ra);

        // undo this change on backtrack
        self.undo.push_if_nonzero(UndoOp::Unmerge {
            a: ra, b: rb,
        });

        // perform actual merge:
        // - a.parents += b.parents
        // - for x in b.class: x.root = a
        // - a.class += b.class
        parents_a.append(&self.tmp_parents);

        let CC0 {cc1, m, b, props, ..} = self;
        cc1.iter_class(rb, |n| {
            trace!("{}.iter_class: update {}", m.pp(rb.0), m.pp(n.id));
            debug_assert_eq!(n.root, rb);
            n.root = ra;

            // if a=true/false, and `n` has a literal, propagate the literal
            if ra.0 == b.true_ && n.as_lit.is_some() {
                let lit = n.as_lit.unwrap();
                trace!("propagate literal {:?} (for true≡{})", lit, m.pp(n.id));
                props.propagate(lit, &[]);
            } else if ra.0 == b.false_ && n.as_lit.is_some() {
                let lit = ! n.as_lit.unwrap();
                trace!("propagate literal {:?} (for false≡{})", lit, m.pp(n.id));
                props.propagate(lit, &[]);
            }
        });

        // ye ole' switcharoo
        {
            let n = &mut self.cc1[ra.0];
            n.prev = prev_b;
            n.next = next_b;

            n.size += size_b;

            let n = &mut self.cc1[rb.0];
            n.prev = prev_a;
            n.next = next_a;
        }

        // check that the merge went well
        if cfg!(debug) {
            let m = self.m.clone();
            self.cc1.iter_class(ra, |n| {
                debug_assert_eq!(n.root, ra, "root of cls({:?})", m.pp(ra.0))
            });
        }
    }

    /// Check and update signature of `t`, possibly adding new merged by congruence.
    fn update_signature(&mut self, t: AST) {
        let CC0 {m, tmp_sig: ref mut sig, cc1, sig_tbl, tasks, ..} = self;
        match m.get().view(t) {
            View::Const(_) => (),
            View::App {f, args} if f == self.b.eq => {
                // do not compute a signature, but check if `args[0]==args[1]`
                let a = args[0];
                let b = args[1];
                if self.cc1.is_eq(a,b) {
                    trace!("merge {} with true by eq-rule", m.pp(t));
                    let expl = Expl::AreEq(a,b);
                    self.tasks.push_back(Task::Merge(t, self.b.true_, expl));
                }
            },
            View::App {f, args} => {
                // compute signature and look for collisions
                sig.compute_app(&cc1, f, args);
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

    /// Main loop for turning explanations into a conflict
    fn expl_fixpoint(&mut self) {
        let m = self.m.clone();
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
                    match (m.get().view(a), m.get().view(b)) {
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
    }

    /// Explain why `a` and `b` were merged, pushing some sub-tasks
    /// onto `self.expl_st`, and leaf literals onto `self.confl`.
    fn explain_eq(&mut self, a: NodeID, b: NodeID)  {
        if a == b { return }
        trace!("explain merge of {} and {}", self.m.pp(a), self.m.pp(b));

        let common_ancestor = self.cc1.find_expl_common_ancestor(a, b);
        trace!("common ancestor: {}", self.m.pp(common_ancestor));
        self.explain_along_path(a, common_ancestor);
        self.explain_along_path(b, common_ancestor);
    }

    /// Explain why `cur =_E ancestor`, where `ancestor` is reachable from `cur`
    fn explain_along_path(&mut self, mut cur: AST, ancestor: AST) {
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

impl<S:Symbol, B:BoolLit> CC1<S,B> {
    fn new(m: &M<S>) -> Self {
        CC1 {
            m: m.clone(),
            nodes: ast::DenseMap::new(node::sentinel()),
            parents: FxHashMap::default(),
            ok: true,
        }
    }

    /// Find representative of the given node
    #[inline(always)]
    fn find(&self, id: NodeID) -> Repr { self[id].root }

    /// Are these two terms known to be equal?
    #[inline(always)]
    fn is_eq(&self, a: NodeID, b: NodeID) -> bool {
        self.find(a) == self.find(b)
    }

    /// Is this term present?
    fn contains_ast(&self, t: AST) -> bool { self.nodes.contains(t) }

    fn parents(&self, r: Repr) -> &ParentList { self.parents.get(&r).unwrap() }
    fn parents_mut(&mut self, r: Repr) -> &mut ParentList { self.parents.get_mut(&r).unwrap() }

    fn perform_undo(&mut self, op: UndoOp) {
        match op {
            UndoOp::SetOk => {
                debug_assert!(! self.ok);
                self.ok = true;
            },
            UndoOp::Unmerge {a, b} => {
                let Node {prev: prev_a, next: next_a, root: root_a, ..} = self[a.0];
                debug_assert!(root_a == a);

                // unmerge b from a
                let nb = &mut self[b.0];
                debug_assert_ne!(nb.root, b);

                // save this to restore `a.node` to its previous state
                let prev_b = nb.prev;
                let next_b = nb.next;
                let size_b = nb.size;

                nb.next = next_a;
                nb.prev = prev_a;
                nb.root = b;

                // one of {ra,rb} points to the other, explanation wise.
                // Be sure to remove this link from the proof forest.
                match nb.expl {
                    Some((ra2,_)) if ra2 == a.0 => nb.expl = None,
                    _ => ()
                }
                {
                    let na = &mut self[a.0];
                    na.prev = prev_b;
                    na.next = next_b;
                    debug_assert!(na.size > size_b);
                    na.size -= size_b;

                    match na.expl {
                        Some((rb2,_)) if rb2 == b.0 => na.expl = None,
                        _ => ()
                    }
                }

                // truncate a's parent list to its previous length
                {
                    let len_parents_b = self.parents(b).len();
                    let p = self.parents_mut(a);
                    debug_assert!(p.len() > len_parents_b);
                    p.truncate(p.len() - len_parents_b);
                }
            },
            UndoOp::RemoveTerm(t) => {
                self.nodes.remove(t);

                // remove from children's parents' lists
                let mr = self.m.get();
                for u in mr.view(t).subterms() {
                    let parents = self.parents.get_mut(&self.find(u)).unwrap();
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

    /// Call `f` with a mutable ref on all nodes of the class of `r`
    fn iter_class<F>(&mut self, r: Repr, mut f: F)
        where F: for<'b> FnMut(&'b mut Node<B>)
    {
        let mut t = r.0;
        loop {
            let n = &mut self[t];
            f(n);

            t = n.next;
            if t == r.0 { break } // done the full loop
        }
    }

    /// Reroot proof forest for the class of `r` so that `r` is the root.
    fn reroot_forest(&mut self, t: NodeID) {
        trace!("reroot {}", self.m.pp(t));
        let (mut cur_t, mut expl) = match &self[t].expl {
            None => {
                return; // rooted in `t` already
            },
            Some((u,e)) => (*u,e.clone()).clone(),
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
    fn dist_to_expl_root(&self, mut t: AST) -> usize {
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
    fn find_expl_common_ancestor(&self, mut a: AST, mut b: AST) -> AST {
        debug_assert!(self.is_eq(a,b));

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
    fn skip_expl_links(&self, mut t: AST, mut n: usize) -> AST {
        while n > 0 {
            if let Some((t2,_)) = self[t].expl { t = t2 } else { panic!() };
            n -= 1
        };
        t
    }
}

impl<S: Symbol,B:BoolLit> backtrack::Backtrackable for CC<S,B> {
    fn push_level(&mut self) {
        trace!("push-level");
        self.cc0.undo.push_level();
        self.cc0.sig_tbl.push_level();
    }

    fn pop_levels(&mut self, n: usize) {
        debug_assert_eq!(self.cc0.undo.n_levels(), self.cc0.sig_tbl.n_levels());
        let cc1 = &mut self.cc0.cc1;
        self.cc0.undo.pop_levels(n, |op| cc1.perform_undo(op));
        self.cc0.sig_tbl.pop_levels(n);
        if n > 0 {
            trace!("pop-levels {}", n);
            self.cc0.tasks.clear(); // changes are invalidated
        }
    }

    fn n_levels(&self) -> usize { self.cc0.undo.n_levels() }
}

impl ParentList {
    fn new() -> Self { ParentList(SVec::new()) }

    #[inline(always)]
    fn len(&self) -> usize { self.0.len() }

    // truncate to old len
    fn truncate(&mut self, n: usize) { self.0.resize(n, NodeID::SENTINEL) }

    fn append(&mut self, other: &ParentList) {
        self.0.extend_from_slice(&other.0);
    }
}

mod cc {
    use super::*;

    impl<S:Symbol,B:BoolLit> std::ops::Index<NodeID> for CC1<S,B> {
        type Output = Node<B>;
        #[inline(always)]
        fn index(&self, id: NodeID) -> &Self::Output {
            self.nodes.get(id).unwrap()
        }
    }

    impl<S:Symbol,B:BoolLit> std::ops::IndexMut<NodeID> for CC1<S,B> {
        #[inline(always)]
        fn index_mut(&mut self, id: NodeID) -> &mut Self::Output {
            self.nodes.get_mut(id).unwrap()
        }
    }

    impl std::ops::Deref for ParentList {
        type Target = SVec<NodeID>;
        fn deref(&self) -> &Self::Target { &self.0 }
    }
    impl std::ops::DerefMut for ParentList {
        fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
    }
}

// manipulating nodes
mod node {
    use super::*;

    /// The default `node` object
    pub(super) fn sentinel<B:BoolLit>() -> Node<B> { Node::new(NodeID::SENTINEL) }

    impl<B:BoolLit> Eq for Node<B> {}
    impl<B:BoolLit> PartialEq for Node<B> {
        fn eq(&self, other: &Node<B>) -> bool { self.id == other.id }
    }

    impl<B:BoolLit> Node<B> {
        /// Create a new node
        pub fn new(id: NodeID) -> Self {
            Node {
                id, prev: id, next: id, expl: None, size: 1,
                root: Repr(id), as_lit: None,
            }
        }
    }
}

mod expl {
    use super::*;

    impl<B:BoolLit> ast::PrettyM for Expl<B> {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
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
}

impl Signature {
    /// Create a new signature.
    fn new() -> Self { Signature(SVec::new()) }

    /// Clear the signature's content.
    #[inline(always)]
    fn clear(&mut self) { self.0.clear() }

    fn compute_app<S:Symbol,B:BoolLit>(&mut self, cc1: &CC1<S,B>, f: AST, args: &[AST]) {
        self.clear();
        self.0.push(cc1.find(f));
        for &u in args {
            self.0.push(cc1.find(u));
        }
    }

}

