
//! AST manager with hashconsing.
//!
//! The AST manager stores AST nodes, referred to via `AST`. These nodes can
//! be used to represent sorts, terms, formulas, theory terms, etc.

extern crate batsmt_core;

pub mod symbol;

use {
    std::{
        slice, u32, marker::PhantomData,
    },
    crate::{symbol::{ SymbolView }},
    batsmt_core::{ ast, GC, AstView, PrettyM },
    fxhash::{FxHashMap,FxHashSet},
    batsmt_pretty as pp,
};

pub use {
    crate::symbol::{ Symbol, str::Sym as StrSymbol, }
};

/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST<S>(u32, PhantomData<S>);

/// A customized view for this particular manager's AST nodes.
pub type View<'a, S:SymbolView<'a>> = AstView<'a, S::View, AST<S>>;

/// A customized view for this particular manager's AST nodes.
pub type ViewSym<'a, S:Symbol> = AstView<'a, &'a S, AST<S>>;

impl<S> AST<S> {
    /// A value of type AST. Only ever use to fill array, do not access.
    pub const SENTINEL : AST<S> = AST(u32::MAX);
}

/// Definition of application keys
///
/// These keys are optimized so that:
/// - they don't need any allocation for "small" applications
/// - they only need to allocate one Box for "big" applications, shared between
///   the map and vector
pub(crate) struct AppStored<'a, S> {
    f: AST<S>,
    len: u16,
    args: app_stored::ArrOrVec<AST<S>>,
    phantom: PhantomData<&'a ()>,
}

mod app_stored {
    use super::*;

    // Number of arguments for a "small" term application
    const N_SMALL_APP : usize = 3;

    #[derive(Copy,Clone)]
    pub(crate) union ArrOrVec<T : Copy> {
        arr: [T; N_SMALL_APP],
        ptr: * const T, // will be shared between vec and hashmap
    }

    fn check_len(len: usize) {
        use std::u16;
        if len > u16::MAX as usize {
            panic!("cannot make an AST application of length {}", len);
        }
    }

    impl<S> AppStored<'static, S> {
        pub fn new(f: AST<S>, args: &[AST<S>]) -> Self {
            let len = args.len();
            check_len(len);

            // copy arguments into local array or heap
            let new_args =
                if len <= N_SMALL_APP {
                    let mut arr = [AST(0); N_SMALL_APP];
                    arr[0..len].copy_from_slice(args);
                    ArrOrVec{arr}
                } else {
                    use std::mem;
                    // go through a vector to allocate on the heap
                    let mut v = Vec::with_capacity(len);
                    v.extend_from_slice(args);
                    debug_assert_eq!(v.capacity(), len);
                    let box_ = v.into_boxed_slice();
                    let ptr = box_.as_ptr(); // access the pointer
                    mem::forget(box_);
                    ArrOrVec{ptr}
                };
            let r = AppStored {
                f, len: len as u16, args: new_args,
                phantom: PhantomData::default(),
            };
            debug_assert_eq!(r.args(), args, "expected {:?} got {:?}", args, r.args());
            r
        }

        // release memory
        pub unsafe fn free(&mut self) {
            let len = self.len as usize;
            if len > N_SMALL_APP {
                // explicitly release memory
                let ptr = self.args.ptr as *mut AST;
                let v = Vec::from_raw_parts(ptr, len, len);
                drop(v)
            }
        }
    }

    impl<'a,S> AppStored<'a,S> {
        #[inline(always)]
        pub fn f(&self) -> AST<S> { self.f }

        #[inline(always)]
        pub fn args<'b: 'a>(&'b self) -> &'b [AST<S>] {
            let len = self.len as usize;
            if len <= N_SMALL_APP {
                unsafe { &self.args.arr[..len] }
            } else {
                unsafe {slice::from_raw_parts(self.args.ptr, len)}
            }
        }

        // Temporary-lived key, borrowing the given slice
        pub fn mk_ref(f: AST<S>, args: &[AST<S>]) -> Self {
            let len = args.len();
            check_len(len);
            let new_args =
                if len <= N_SMALL_APP {
                    let mut arr = [AST(0); N_SMALL_APP];
                    arr[0..len].copy_from_slice(args);
                    ArrOrVec{arr}
                } else {
                    ArrOrVec{ptr: args.as_ptr()}
                };
            let r = AppStored {
                f, len: len as u16, args: new_args,
                phantom: PhantomData::default(),
            };
            debug_assert_eq!(r.args(), args, "expected {:?} got {:?}", args, r.args());
            r
        }

        pub fn to_owned(self) -> AppStored<'static, S> {
            AppStored::new(self.f, self.args())
        }
    }

    impl<S> Copy for AppStored<'static,S> {}
    impl<S> Clone for AppStored<'static,S> {
        fn clone(&self) -> Self { *self }
    }

    impl<'a,S> Eq for AppStored<'a,S> {}
    impl<'a,S> PartialEq for AppStored<'a,S> {
        fn eq(&self, other: &AppStored<'a,S>) -> bool {
            self.f == other.f && self.args() == other.args()
        }
    }

    use std::hash::{Hash,Hasher};

    impl<'a,S> Hash for AppStored<'a,S> {
        fn hash<H:Hasher>(&self, h: &mut H) {
            self.f.hash(h);
            self.args().hash(h)
        }
    }

    use std::fmt::{Debug,self};

    impl<'a,S> Debug for AppStored<'a,S> {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "({:?} {:?})", self.f, self.args())
        }
    }
}

// The kind of object stored in a given slot
#[repr(u8)]
#[derive(Copy,Clone,Debug,Eq,PartialEq,Hash)]
pub(crate) enum Kind { Undef, App, Sym, }

/// The definition of a node
#[derive(Clone)]
struct NodeStored<S:Symbol> {
    pub(crate) kind: Kind,
    data: node_stored::Data<S>,
}

// helper to make a view from a stored node
fn view_node<'a, S>(n: &'a NodeStored<S>) -> View<'a,S> where S : Symbol {
    match n.kind() {
        Kind::App => {
            let k = unsafe {n.as_app()};
            View::App {f: k.f(), args: k.args()}
        },
        Kind::Sym => {
            View::Const(unsafe {n.as_sym()}.view())
        },
        Kind::Undef => panic!("cannot access undefined AST"),
    }
}

// helper to make a view from a stored node
fn view_sym_node<'a, S>(n: &'a NodeStored<S>) -> ViewSym<'a,S> where S : Symbol {
    match n.kind() {
        Kind::App => {
            let k = unsafe {n.as_app()};
            ViewSym::App {f: k.f(), args: k.args()}
        },
        Kind::Sym => {
            ViewSym::Const(unsafe {n.as_sym()})
        },
        Kind::Undef => panic!("cannot access undefined AST"),
    }
}

mod node_stored {
    use super::*;

    #[derive(Copy,Clone)]
    pub(crate) union Data<SPtr : Copy> {
        pub undef: (),
        pub app: AppStored<'static, SPtr>,
        pub sym: SPtr, // raw pointer to a symbol
    }

    impl<S:Symbol> NodeStored<S> {
        /// Make a constant node from a symbol
        pub fn mk_sym(sym: S::Owned) -> Self {
            let ptr = unsafe { S::to_ptr(sym) };
            NodeStored {data: Data{sym: ptr}, kind: Kind::Sym }
        }
        pub fn mk_app(app: AppStored<'static, S>) -> Self {
            NodeStored {kind: Kind::App, data: Data { app }}
        }

        #[inline(always)]
        pub fn kind(&self) -> Kind { self.kind }

        #[inline(always)]
        pub fn is_app(&self) -> bool { self.kind() == Kind::App }
        #[inline(always)]
        pub fn is_sym(&self) -> bool { self.kind() == Kind::Sym }

        pub unsafe fn as_app(&self) -> &AppStored<'static, S> {
            debug_assert!(self.kind() == Kind::App);
            &self.data.app
        }

        // view as a string symbol
        pub unsafe fn as_sym(&self) -> S {
            debug_assert!(self.kind() == Kind::Sym);
            self.data.sym
        }

        /// release resources
        pub unsafe fn free(&mut self) {
            match self.kind {
                Kind::Undef => (),
                Kind::App => self.data.app.free(),
                Kind::Sym => {
                    let ptr = self.data.sym;
                    S::free(ptr)
                },
            }
        }
    }
}

// free memory for this node, including its hashmap entry if any
unsafe fn free_node<S:Symbol>(
    tbl: &mut FxHashMap<AppStored<'static,S>, AST<S>>,
    mut n: NodeStored<S>)
{
    if n.kind() == Kind::App {
        let app = n.as_app();
        // remove from table
        tbl.remove_entry(&app);
    }
    n.free();
}

/// The AST manager, responsible for storing and creating AST nodes
pub struct Manager<S:Symbol> {
    nodes: Vec<NodeStored<S>>,
    tbl_app: FxHashMap<AppStored<'static,S>, AST<S>>, // for hashconsing
    // TODO: use some bits of nodes[i].kind (a u8) for this?
    gc_alive: BitSet, // for GC
    gc_stack: Vec<AST<S>>, // temporary vector for GC marking
    recycle: Vec<u32>, // indices that contain a `undefined`
}

mod manager {
    use super::*;

    impl<S:Symbol> ast::Manager for Manager<S> {
        type AST = AST<S>;

        #[inline(always)]
        fn view(&self, t: &AST<S>) -> View<S> {
            self.view(t)
        }

    }

    /* FIXME
    /// The public interface of the manager.
    ///
    /// A `Manager<S>` is a shared pointer to the actual data.
    /// Use `get` or `get_mut` to gain access to the internals.
    impl<S:Symbol> Manager<S> {
        /// Temporary reference
        #[inline(always)]
        pub fn get<'a>(&'a self) -> ManagerRef<'a, S> {
            ManagerRef(self.0.borrow())
        }

        /// Temporary mutable reference
        #[inline(always)]
        pub fn get_mut<'a>(&'a self) -> ManagerRefMut<'a, S> {
            ManagerRefMut(self.0.borrow_mut())
        }

        /// Number of terms
        pub fn n_terms(&self) -> usize { self.get().n_terms() }

        #[inline(always)]
        pub fn mk_app(&self, f: AST, args: &[AST]) -> AST {
            self.get_mut().mk_app(f, args)
        }

        #[inline(always)]
        pub fn mk_sym(&self, s: S::Owned) -> AST { self.get_mut().mk_sym(s) }

        /// Create a new (single-thread) manager
        pub fn new() -> Self {
            let m = ManagerCell::new();
            Manager(Shared::new(m))
        }

        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// Allocates a `iter_dag::State` and uses it to iterate only once.
        /// For more sophisticated use (iterating on several terms, etc.)
        /// use `iter_dag::State` directly.
        pub fn iter_dag<F>(&self, t: AST, f: F) where F: FnMut(&Self, AST) {
            let mut st = iter_dag::State::new(self);
            st.iter(t, f)
        }

        /// Iterate over the given AST `t`,
        /// calling `fexit` once on every subterm satisfying `fenter`, in suffix order.
        ///
        /// - this traverses subterms before superterms.
        /// - if a term does not satisfy `fenter`, its subterms are not explored.
        /// - `ctx` is carried around and passed to both `fexit` and `fenter`
        ///
        /// For more sophisticated use (iterating on several terms, etc.)
        /// use `iter_suffix::State` directly.
        pub fn iter_suffix<Ctx,F1,F2>(
            &self, t: AST, ctx: &mut Ctx, fenter: F1, fexit: F2
        )
            where F1: FnMut(&mut Ctx, AST) -> bool, F2: FnMut(&mut Ctx, AST)
        {
            let mut st = iter_suffix::State::new(self);
            st.iter(t, ctx, fenter, fexit)
        }

        /// Iterate over the given AST `t`, mapping every subterm using `f`.
        ///
        /// Allocates a `map_dag::State` and uses it to iterate.
        /// For more sophisticated use (mapping several terms, etc.)
        /// use `map_dag::State` directly.
        pub fn map<F,R>(&self, t: AST, f: F) -> R
            where R: Clone,
                  F: for<'a> FnMut(&Manager<S>, AST, MapView<R>) -> R
        {
            let mut st = map_dag::State::new(self);
            st.map(t, f)
        }

        /// Compute size of the term, seen as a DAG.
        ///
        /// Each unique subterm is counted only once.
        pub fn size_dag(&self, t: AST) -> usize {
            let mut n = 0;
            self.iter_dag(t, |_,_| { n += 1 });
            n
        }

        /// Compute size of the term, seen as a tree.
        pub fn size_tree(&self, t: AST) -> usize {
            self.map(t, |_m, _u, view| {
                match view {
                    MapView::Const => 1usize,
                    MapView::App{f, args} => {
                        args.iter().fold(1 + *f, |x,y| x+y) // 1+sum of sizes
                    },
                }
            })
        }
    }
    */

    impl<S:Symbol> Manager<S> {
        // node for undefined slots, should never be exposed
        const UNDEF : NodeStored<S> =
            NodeStored { kind: Kind::Undef, data: node_stored::Data {undef: ()}, };

        /// Create a new AST manager
        pub(crate) fn new() -> Self {
            let mut tbl_app = FxHashMap::default();
            tbl_app.reserve(1_024);
            Manager {
                nodes: Vec::with_capacity(512),
                tbl_app,
                gc_alive: BitSet::new(),
                gc_stack: Vec::new(),
                recycle: Vec::new(),
            }
        }

        /// View the given AST node
        #[inline(always)]
        pub fn view(&self, ast: AST<S>) -> View<S> {
            view_node(&self.nodes[ast.0 as usize])
        }

        /// View the given AST node
        #[inline(always)]
        pub fn view_sym(&self, ast: AST<S>) -> ViewSym<S> {
            view_sym_node(&self.nodes[ast.0 as usize])
        }

        #[inline(always)]
        pub fn is_app(&self, ast: AST<S>) -> bool {
            self.nodes[ast.0 as usize].is_app()
        }

        #[inline(always)]
        pub fn is_sym(&self, ast: AST<S>) -> bool {
            self.nodes[ast.0 as usize].is_sym()
        }

        /// Number of terms
        pub fn n_terms(&self) -> usize {
            let nlen = self.nodes.len();
            let rlen = self.recycle.len();
            debug_assert!(nlen >= rlen);
            nlen - rlen
        }

        // allocate a new AST ID, and return the slot it should live in
        fn allocate_id(&mut self) -> (AST<S>, &mut NodeStored<S>) {
            match self.recycle.pop() {
                Some(n) => {
                    let ast = AST(n);
                    let slot = &mut self.nodes[n as usize];
                    debug_assert!(slot.kind() == Kind::Undef);
                    (ast,slot)
                },
                None => {
                    let n = self.nodes.len();
                    // does `n` fit in an AST?
                    if n > u32::MAX as usize {
                        panic!("cannot allocate more AST nodes")
                    }
                    self.nodes.push(Self::UNDEF);
                    let slot = &mut self.nodes[n];
                    (AST(n as u32), slot)
                }
            }
        }

        /// `m.mk_app(f, args)` creates the application of `f` to `args`.
        ///
        /// If the term is structurally equal to an existing term, then this
        /// ensures the exact same AST is returned ("hashconsing").
        /// If `args` is empty, return `f`.
        pub fn mk_app(&mut self, f: AST<S>, args: &[AST<S>]) -> AST<S> {
            if args.len() == 0 { return f }

            let k = AppStored::mk_ref(f, args);

            // borrow multiple fields
            let nodes = &mut self.nodes;
            let tbl_app = &mut self.tbl_app;
            //let ManagerInterface {ref mut apps, ref mut tbl_app,..} = self;

            match tbl_app.get(&k) {
                Some(&a) => a, // fast path
                None => {
                    // insert
                    let n = nodes.len();
                    let ast = AST(n as u32);
                    // make 2 owned copies of the key
                    let k1 = k.to_owned();
                    let k2 = k1.clone();
                    nodes.push(NodeStored::mk_app(k1));
                    tbl_app.insert(k2, ast);
                    // return AST
                    ast
                }
            }
        }

        /// Make a term from a symbol.
        ///
        /// Note that calling this function twice with the same symbol
        /// will result in two distinct ASTs (as if the second one
        /// was shadowing the first). Use an auxiliary hashtable if
        /// you want sharing.
        pub fn mk_sym(&mut self, s: S::Owned) -> AST<S> {
            let (ast, slot) = self.allocate_id();
            *slot = NodeStored::mk_sym(s);
            ast
        }

        /// Iterate over all the ASTs and their definition
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=(AST, View<'a,S>)> + 'a
        {
            self.nodes.iter().enumerate()
                .filter_map(move |(i,n)| {
                    let a = AST(i as u32);
                    match n.kind {
                        Kind::Undef => None, // skip empty slot
                        _ => Some((a, view_node(n))),
                    }
                })
        }

        /// Iterate over all the ASTs
        pub fn iter_ast<'a>(&'a self) -> impl Iterator<Item=AST> + 'a {
            self.nodes.iter().enumerate()
                .filter_map(|(i,n)| {
                    let a = AST(i as u32);
                    match n.kind {
                        Kind::Undef => None, // skip empty slot
                        _ => Some(a),
                    }
                })
        }

        // traverse and mark all elements on `stack` and their subterms
        fn gc_traverse_and_mark(&mut self) {
            while let Some(ast) = self.gc_stack.pop() {
                if self.gc_alive.get(ast) {
                    continue; // subgraph already marked and traversed
                }
                self.gc_alive.add(ast);

                match view_node(&self.nodes[ast.0 as usize]) {
                    View::Const(_) => (),
                    View::App{f, args} => {
                        // explore subterms, too
                        self.gc_stack.push(f);
                        for &a in args { self.gc_stack.push(a) };
                    }
                }
            }
        }

        // collect dead values, return number of collected values
        fn gc_retain_roots(&mut self) -> usize {
            use std::mem;
            let mut count = 0;

            let len = self.nodes.len();
            for i in 0 .. len {
                match self.nodes[i].kind() {
                    Kind::Undef => (),
                    _ if self.gc_alive.get(AST(i as u32)) => (), // keep
                    _ => {
                        // collect
                        count += 1;
                        // remove node from `self.nodes[i]` and move it locally
                        let mut n = Self::UNDEF;
                        mem::swap(&mut self.nodes[i], &mut n);
                        // free memory of `n`, remove it from hashtable
                        unsafe { free_node(&mut self.tbl_app, n); }
                        self.nodes[i] = Self::UNDEF;
                        self.recycle.push(i as u32)
                    }
                }
            }
            count
        }

        fn gc_mark_root(&mut self, &ast: &AST<S>) {
            // mark subterms transitively, using recursion stack
            let marked = self.gc_alive.get(ast);
            if !marked {
                self.gc_stack.push(ast);
                self.gc_traverse_and_mark();
            }
        }

        fn gc_collect(&mut self) -> usize {
            let n = self.gc_retain_roots();
            self.gc_alive.clear();
            n
        }
    }

    impl<S> Manager<S> where S:Symbol, S::Owned : for<'a> From<&'a str> {
        /// Make a symbol node from a string
        pub fn mk_str(&mut self, s: &str) -> AST<S> {
            let sym: S::Owned = s.into();
            self.mk_sym(sym)
        }
    }

    impl<S> Manager<S> where S:Symbol, S::Owned : From<String> {
        /// Make a symbol node from a owned string
        pub fn mk_string(&mut self, s: String) -> AST<S> {
            let sym: S::Owned = s.into();
            self.mk_sym(sym)
        }
    }

    /// GC for a manager's internal nodes
    impl<S> GC for Manager<S> where S: Symbol {
        type Element = AST<S>;

        fn mark_root(&mut self, ast: &AST<S>) {
            self.get_mut().gc_mark_root(ast)
        }

        fn collect(&mut self) -> usize {
            self.get_mut().gc_collect()
        }
    }

    /// An AST can be printed, given a manager, if the symbols are pretty
    impl<S:Symbol> PrettyM for AST<S> {
        type M = Manager<S>;
        fn pp_m(&self, m: &Manager<S>, ctx: &mut pp::Ctx) {
            match m.get().view_sym(*self) {
                ViewSym::Const(s) => s.pp(ctx),
                ViewSym::App{f,args} if args.len() == 0 => {
                    ctx.pp(&m.pp(f)); // just f
                },
                ViewSym::App{f,args} => {
                    ctx.sexp(|ctx| {
                        ctx.pp(&m.pp(f)).space();
                        ctx.iter(" ", args.iter().map(|u| m.pp(*u)));
                    });
                }
            }
            if ctx.alternate() {
                ctx.string(format!("/{}", self.0)); // print unique ID
            }
        }
    }
}

/// A bitset whose elements are AST nodes
pub struct BitSet(::bit_set::BitSet);

mod bit_set {
    use super::*;
    use std::ops::Deref;

    // TODO: impl AstDenseSet
    impl BitSet {
        /// New bitset
        #[inline(always)]
        pub fn new() -> Self { BitSet(::bit_set::BitSet::new()) }

        /// Clear all bits.
        #[inline(always)]
        pub fn clear(&mut self) { self.0.clear() }

        #[inline(always)]
        pub fn len(&self) -> usize { self.0.len () }

        #[inline(always)]
        pub fn get<S>(&self, ast: AST<S>) -> bool {
            self.0.contains(ast.0 as usize)
        }

        #[inline]
        pub fn add<S>(&mut self, ast: AST<S>) { self.0.insert(ast.0 as usize); }

        #[inline]
        pub fn remove<S>(&mut self, ast: AST<S>) { self.0.remove(ast.0 as usize); }

        pub fn add_slice<S>(&mut self, arr: &[AST<S>]) {
            for &ast in arr { self.add(ast) }
        }

        /// Add all the ASTs in the given iterator
        pub fn add_iter<S, Q, I>(&mut self, iter:I)
            where I: Iterator<Item=Q>, Q: Deref<Target=AST<S>>
        {
            for ast in iter {
                self.add(*ast)
            }
        }
    }
}

/// A hashmap whose keys are AST nodes
pub type HashMap<S, V> = ast::AstHashMap<AST<S>, V>;

/// A hashset whose keys are AST nodes
pub type HashSet<S> = FxHashSet<AST<S>>;

/* FIXME
 *
 * implement AstDenseMap class
mod dense_map {
    use super::*;
    use ::bit_set::BitSet;

    /// An AST map backed by an array, with a default value
    #[derive(Clone)]
    pub struct T<V : Clone> {
        sentinel: V,
        mem: BitSet,
        vec: Vec<V>,
        len: usize, // number of elements
    }

    impl<V : Clone> T<V> {
        /// Create a new map with `sentinel` as an element to fill the underlying storage.
        ///
        /// It is best if `sentinel` is efficient to clone.
        pub fn new(sentinel: V) -> Self {
            DenseMap {sentinel, mem: BitSet::new(), vec: Vec::new(), len: 0, }
        }

        /// Access the given key
        pub fn get(&self, ast: AST<S>) -> Option<&V> {
            let i = ast.0 as usize;
            if self.mem.contains(i) {
                debug_assert!(i < self.vec.len());
                Some(&self.vec[i])
            } else {
                None
            }
        }

        /// Access two disjoint locations, mutably.
        ///
        /// Precondition: the ASTs are distinct and in the map (panics otherwise).
        pub fn get2(&mut self, t1: AST, t2: AST) -> (&mut V, &mut V) {
            let t1 = t1.0 as usize;
            let t2 = t2.0 as usize;

            if t1 == t2 || !self.mem.contains(t1) || !self.mem.contains(t2) {
                panic!("dense_map.get2: invalid access");
            }

            let ref1 = (&mut self.vec[t1]) as *mut V;
            let ref2 = (&mut self.vec[t2]) as *mut V;
            // this is correct because t1 != t2, so the pointers are disjoint.
            unsafe { (&mut* ref1, &mut *ref2) }
        }

        /// Access the given key, return a mutable reference to its value
        pub fn get_mut(&mut self, ast: AST) -> Option<&mut V> {
            let i = ast.0 as usize;
            if self.mem.contains(i) {
                debug_assert!(i < self.vec.len());
                Some(&mut self.vec[i])
            } else {
                None
            }
        }

        /// Does the map contain this key?
        pub fn contains(&self, ast: AST) -> bool {
            let i = ast.0 as usize;
            self.mem.contains(i)
        }

        /// Insert a value
        pub fn insert(&mut self, ast: AST, v: V) {
            let i = ast.0 as usize;
            let len = self.vec.len();
            // resize arrays if required
            if len <= i {
                self.vec.resize(i+1, self.sentinel.clone());
            }
            debug_assert!(self.vec.len() > i);
            self.vec[i] = v;
            let is_new = self.mem.insert(i);
            if is_new {
                self.len += 1;
            }
        }

        /// Is the map empty?
        #[inline(always)]
        pub fn is_empty(&self) -> bool { self.len == 0 }

        /// Remove all bindings
        pub fn clear(&mut self) {
            self.len = 0;
            self.vec.clear();
            self.mem.clear();
        }

        /// Remove the given key
        pub fn remove(&mut self, ast: AST) {
            let i = ast.0 as usize;

            if self.mem.contains(i) {
                self.mem.remove(i);
                self.vec[i] = self.sentinel.clone();

                debug_assert!(self.len > 0);
                self.len -= 1;
            }
        }

        /// Number of elements
        #[inline(always)]
        pub fn len(&self) -> usize {
            self.len
        }

        /// Iterate over key/value pairs
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=(AST, &'a V)> + 'a {
            self.vec.iter().enumerate().filter_map(move |(i,v)| {
                if self.mem.contains(i) {
                    let a = AST(i as u32);
                    Some((a,v))
                } else {
                    None
                }
            })
        }
    }
}

/// A map backed by a vector
///
/// We assume the existence of a `sentinel` value that is used to fill the
/// vector.
pub type DenseMap<V> = dense_map::T<V>;
*/

// check that `Manager` is just pointer-sized
#[test]
fn test_size_manager() {
    use crate::StrSymbol as S;
    use std::mem;
    assert_eq!(mem::size_of::<Manager<S>>(), mem::size_of::<*const u32>());
}
