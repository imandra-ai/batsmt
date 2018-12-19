
//! Congruence closure.
//!
//! The `CC` type is responsible for enforcing congruence and transitivity
//! of equality.

// TODO: signatures
// TODO: parametrize by "micro theories" (which just work on merges + expl)

use {
    std::{
        //ops::{Deref,DerefMut},
        marker::PhantomData,
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
    props: PropagationSet<B>,
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
    traverse: ast::iter_suffix::State<S>, // for recursive traversal
    expl_st: Vec<Expl<B>>, // to expand explanations
    cc1: CC1<S,B>,
}

/// internal state
struct CC1<S:Symbol,B:BoolLit> {
    m: ast::Manager<S>, // the AST manager
    ok: bool, // no conflict?
    nodes: ast::DenseMap<Node<B>>,
    parents: FxHashMap<Repr, ParentList>, // parents of the given class
}

/// One node in the congruence closure's E-graph
#[derive(Clone)]
struct Node<B:BoolLit> {
    id: NodeID,
    cls_next: NodeID,
    cls_prev: NodeID,
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

type Merge = (Repr,Repr);
type Merges = SVec<Merge>;

/// An explanation for a merge
#[derive(Clone)]
enum Expl<B> {
    Lit(B),
    Merges(Merges), // congruence, injectivity, etc.
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
        a_len_parents: usize, // old length of `a.parents`
    }, // unmerge these two reprs
}

/// Operation to perform in the main fixpoint
enum Task<B> {
    AddTerm(AST), // add term if not present
    MapToLit(AST,B), // map term to lit
    UpdateSig(AST), // re-check signature
    Merge(AST, AST, Expl<B>), // merge the classes of these two terms
    Distinct(SVec<AST>, Expl<B>),
}

// implement main interface
impl<S:Symbol, B:BoolLit> CCInterface<B> for CC<S,B> {
    fn merge(&mut self, t1: AST, t2: AST, lit: B) {
        let expl = Expl::Lit(lit);
        let tasks = &mut self.cc0.tasks;
        tasks.push_back(Task::AddTerm(t1));
        tasks.push_back(Task::AddTerm(t2));
        tasks.push_back(Task::Merge(t1,t2,expl))
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
        self.cc0.tasks.push_back(Task::MapToLit(t, lit))
    }

    fn impl_descr(&self) -> &'static str { "fast congruence closure"}
}

// main API
impl<S, B:BoolLit> CC<S, B> where S: Symbol {
    /// Create a new congruence closure using the given `Manager`
    pub fn new(m: &ast::Manager<S>, b: Builtins) -> Self {
        CC {
            m_s: PhantomData::default(),
            props: PropagationSet::new(),
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
        Ok(&self.props)
    }
}

/// Does `t` need to be entered in the signature table?
fn needs_signature<S:Symbol>(m: &M<S>, t: AST) -> bool {
    match m.get().view(t) {
        View::Const(_) => false,
        View::App{..} => true,
    }
}

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
            undo: backtrack::Stack::new(),
            tmp_parents: ParentList::new(),
            traverse: ast::iter_suffix::State::new(m),
            expl_st: vec!(),
            cc1,
        }
    }

    fn find(&self, id: NodeID) -> Repr { self.cc1.find(id) }
    fn is_root(&self, id: NodeID) -> bool { self.find(id).0 == id }

    /// Return list of parents for `r`.
    fn parents(&self, r: Repr) -> &ParentList {
        self.cc1.parents(r)
    }

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
                undo.push(UndoOp::RemoveTerm(t));

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
            self.undo.push(UndoOp::UnmapLit(t));
        }
    }

    /// Merge `a` and `b`, if they're not already equal.
    fn merge(&mut self, a: AST, b: AST, expl: Expl<B>) {
        debug_assert!(self.cc1.contains_ast(a));
        debug_assert!(self.cc1.contains_ast(b));

        let mut ra = self.cc1.find(a);
        let mut rb = self.cc1.find(b);
        debug_assert!(self.is_root(ra.0), "repr({:?}) = {:?}", a, ra);
        debug_assert!(self.is_root(rb.0), "repr({:?}) = {:?}", b, rb);

        if ra != rb {
            let size_a = self.parents(ra).len();
            let size_b = self.parents(rb).len();

            // merge smaller one into bigger one, except that booleans are
            // always representatives
            if rb.0 == self.b.true_ || rb.0 == self.b.false_ {
                // conflict: merge true with false (since they are distinct)
                if ra.0 == self.b.true_ || ra.0 == self.b.false_ {
                    // generate conflict from `expl`, `a == ra`, `b == rb`
                    trace!("generate conflict from merge of true/false from {:?} and {:?}",
                           self.m.pp(a), self.m.pp(b));
                    self.cc1.ok = false;
                    self.undo.push(UndoOp::SetOk);
                    self.confl.clear();
                    self.expand_expl_into_confl(expl);
                    self.explain_eq(a, ra.0);
                    self.explain_eq(b, rb.0);
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
            self.cc1.reroot_forest(rb);
            self.cc1[rb.0].expl = Some((ra.0, expl));

            // local copy of parents(b)
            self.tmp_parents.clear();
            self.tmp_parents.append(&self.cc1.parents(rb));

            let parents_a = self.cc1.parents_mut(ra);
            let a_len_parents = parents_a.len(); // save `parents(a).len`

            // undo this change on backtrack
            self.undo.push(UndoOp::Unmerge {
                a: ra, b: rb, a_len_parents,
            });

            // perform actual merge:
            // - a.parents += b.parents
            // - for x in b.class: x.root = a; update-sig(x)
            parents_a.append(&self.tmp_parents);
            let CC0 {tasks, cc1, m, ..} = self;
            cc1.iter_class(rb, |n| {
                debug_assert_eq!(n.root, rb);
                n.root = ra;

                // might need to check for congruence
                if needs_signature(m, n.id) {
                    tasks.push_back(Task::UpdateSig(n.id));
                }

                // TODO: if a=true/false, and `n` has a literal, propagate the literal
            });

            // check that the merge went well
            if cfg!(debug) {
                let m = self.m.clone();
                self.cc1.iter_class(ra, |n| {
                    debug_assert_eq!(n.root, ra, "root of cls({:?})", m.pp(ra.0))
                });
            }
        }
    }

    /// Check and update signature of `t`, possibly adding new merged by congruence.
    fn update_signature(&mut self, t: AST) {
        // FIXME
        unimplemented!("update signature {}", self.m.pp(t));

        // TODO: also the place to check for `(= a b)` where a==b ----> merge with true
        // TODO: do not do normal signatures for `(= a b)` otherwise
    }

    /// Unfold `expl` into literals, push them into `self.confl`
    fn expand_expl_into_confl(&mut self, expl: Expl<B>) {
        self.expl_st.clear();
        self.expl_st.push(expl);
        while let Some(e) = self.expl_st.pop() {
            match e {
                Expl::Lit(lit) => self.confl.push(lit),
                Expl::Merges(v) => {
                    for (ra,rb) in v.iter() {
                        self.explain_eq(ra.0, rb.0);
                    }
                }
            }
        }
    }

    /// Explain why `a` and `b` were merged, pushing explanations onto `self.expl_st`.
    fn explain_eq(&mut self, a: NodeID, b: NodeID)  {
        unimplemented!("explain merge {} {}", self.m.pp(a), self.m.pp(b));
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
            UndoOp::Unmerge {a, b, a_len_parents} => {
                debug_assert!(self[a.0].is_root());
                // unmerge b from a
                let n = &mut self[b.0];

                debug_assert!(! n.is_root());
                n.root = b;

                // one of {ra,rb} points to the other, explanation wise.
                // Be sure to remove this link from the proof forest.
                match n.expl {
                    Some((ra2,_)) if ra2 == a.0 => n.expl = None,
                    _ => ()
                }
                {
                    let na = &mut self[a.0];
                    match na.expl {
                        Some((rb2,_)) if rb2 == b.0 => na.expl = None,
                        _ => ()
                    }
                }

                // truncate a's parent list to its previous len
                self.parents_mut(a).truncate(a_len_parents);
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

            t = n.cls_next;
            if t == r.0 { break } // done the full loop
        }
    }

    /// Reroot proof forest for the class of `r` so that `r` is the root.
    fn reroot_forest(&mut self, r: Repr) {
        let (mut cur, mut expl) = match &self[r.0].expl {
            None => {
                return; // rooted in `t` already
            },
            Some((u,e)) => (*u,e.clone()),
        };

        let mut prev = r.0;
        loop {
            let cur_node = &mut self[cur];
            let mut expl_tup = Some((prev,expl));
            std::mem::swap(&mut cur_node.expl, &mut expl_tup);

            // `expl_tup` now points to `cur`'s former pointer.
            match expl_tup {
                None => break,
                Some((next, expl_next)) => {
                    // follow pointer
                    prev = cur;
                    cur = next;
                    expl = expl_next;
                },
            }
        }
    }
}

impl<S: Symbol,B:BoolLit> backtrack::Backtrackable for CC<S,B> {
    fn push_level(&mut self) {
        self.cc0.undo.push_level();
    }

    fn pop_levels(&mut self, n: usize) {
        let cc1 = &mut self.cc0.cc1;
        self.cc0.undo.pop_levels(n, |op| cc1.perform_undo(op));
        if n > 0 {
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

// main congruence closure operations
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
                id, cls_prev: id, cls_next: id, expl: None,
                root: Repr(id), as_lit: None,
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

    impl<B:BoolLit> ast::PrettyM for Expl<B> {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            match self {
                Expl::Lit(lit) => {
                    ctx.str("lit(").debug(lit).str(")");
                },
                Expl::Merges(vs) => {
                    ctx.str("merges(");
                    for (r1,r2) in vs.iter() {
                        ctx.str("(= ").pp(&m.pp(r1.0)).str(" ").pp(&m.pp(r2.0)).str(")");
                    }
                    ctx.str(")");
                }
            }
        }
    }
}

