
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
    batsmt_core::{ ast::{self, AstDenseMap, Manager, AstSet, }, gc, AstView, },
    fxhash::{FxHashMap,FxHashSet},
    batsmt_pretty as pp,
};

pub use {
    crate::symbol::{ SymbolCtx, SymbolManager, str::StrManager as StrSymbolManager, }
};

/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST(u32);

pub type HView<'a, S:SymbolManager> = AstView<'a, &'a S::View, AST>;

impl AST {
    /// A value of type AST. Only ever use to fill array, do not access.
    pub const SENTINEL : AST = AST(u32::MAX);
}

/// Definition of application keys
///
/// These keys are optimized so that:
/// - they don't need any allocation for "small" applications
/// - they only need to allocate one Box for "big" applications, shared between
///   the map and vector
#[derive(Copy,Clone)]
struct AppStored<'a> {
    f: AST,
    len: u16,
    args: app_stored::ArrOrVec<AST>,
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

    impl AppStored<'static> {
        pub fn new(f: AST, args: &[AST]) -> Self {
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

    impl<'a> AppStored<'a> {
        #[inline(always)]
        pub fn f(&self) -> AST { self.f }

        #[inline(always)]
        pub fn args<'b: 'a>(&'b self) -> &'b [AST] {
            let len = self.len as usize;
            if len <= N_SMALL_APP {
                unsafe { &self.args.arr[..len] }
            } else {
                unsafe {slice::from_raw_parts(self.args.ptr, len)}
            }
        }

        // Temporary-lived key, borrowing the given slice
        pub fn mk_ref(f: AST, args: &[AST]) -> Self {
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

        pub fn to_owned(self) -> AppStored<'static> {
            AppStored::new(self.f, self.args())
        }
    }

    impl<'a> Eq for AppStored<'a> {}
    impl<'a> PartialEq for AppStored<'a> {
        fn eq(&self, other: &AppStored<'a>) -> bool {
            self.f == other.f && self.args() == other.args()
        }
    }

    use std::hash::{Hash,Hasher};

    impl<'a> Hash for AppStored<'a> {
        fn hash<H:Hasher>(&self, h: &mut H) {
            self.f.hash(h);
            self.args().hash(h)
        }
    }

    use std::fmt::{Debug,self};

    impl<'a> Debug for AppStored<'a> {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "({:?} {:?})", self.f, self.args())
        }
    }
}

// The kind of object stored in a given slot
#[repr(u8)]
#[derive(Copy,Clone,Debug,Eq,PartialEq,Hash)]
enum Kind { Undef, App, Sym, }

/// The definition of a node
#[derive(Clone)]
struct NodeStored<S:SymbolManager> {
    pub(crate) kind: Kind,
    data: NodeStoredData<S::Ref>,
}

#[derive(Copy,Clone)]
union NodeStoredData<SPtr : Copy> {
    pub undef: (),
    pub app: AppStored<'static>,
    pub sym: SPtr, // raw pointer to a symbol
}

// helper to make a view from a stored node
fn view_node<'a, S>(sym: &'a S, n: &'a NodeStored<S>)
    -> HView<'a, S> where S : SymbolManager
{
    match n.kind() {
        Kind::App => {
            let k = unsafe {n.as_app()};
            AstView::App {f: k.f(), args: k.args()}
        },
        Kind::Sym => {
            AstView::Const(unsafe { sym.view(n.as_sym()) })
        },
        Kind::Undef => panic!("cannot access undefined AST"),
    }
}

mod node_stored {
    use super::*;

    impl<S:SymbolManager> NodeStored<S> {
        /// Make a constant node from a symbol
        pub fn mk_sym(sym: S::Ref) -> Self {
            NodeStored {data: NodeStoredData{sym}, kind: Kind::Sym }
        }
        pub fn mk_app(app: AppStored<'static>) -> Self {
            NodeStored {kind: Kind::App, data: NodeStoredData { app }}
        }

        #[inline(always)]
        pub fn kind(&self) -> Kind { self.kind }

        #[inline(always)]
        pub fn is_app(&self) -> bool { self.kind() == Kind::App }
        #[inline(always)]
        pub fn is_sym(&self) -> bool { self.kind() == Kind::Sym }

        pub unsafe fn as_app(&self) -> &AppStored<'static> {
            debug_assert!(self.kind() == Kind::App);
            &self.data.app
        }

        // view as a symbol
        pub unsafe fn as_sym(&self) -> S::Ref {
            debug_assert!(self.kind() == Kind::Sym);
            self.data.sym
        }

        /// release resources
        pub unsafe fn free(&mut self, sym_m: &mut S) {
            match self.kind {
                Kind::Undef => (),
                Kind::App => self.data.app.free(),
                Kind::Sym => {
                    let ptr = self.data.sym;
                    sym_m.free(ptr);
                },
            }
        }
    }
}

// free memory for this node, including its hashmap entry if any
unsafe fn free_node<S:SymbolManager>(
    tbl_app: &mut FxHashMap<AppStored<'static>, AST>,
    sym_m: &mut S,
    mut n: NodeStored<S>)
{
    match n.kind() {
        Kind::App => {
            let app = n.as_app();
            // remove from table
            tbl_app.remove_entry(&app);
        },
        _ => (),
    };
    n.free(sym_m);
}

/// The AST manager, responsible for storing and creating AST nodes
pub struct HManager<S:SymbolManager> {
    nodes: Vec<NodeStored<S>>,
    tbl_app: FxHashMap<AppStored<'static>, AST>, // hashconsing of applications
    sym_m: S,
    // TODO: use some bits of nodes[i].kind (a u8) for this?
    gc_alive: BitSet, // for GC
    gc_stack: Vec<AST>, // temporary vector for GC marking
    recycle: Vec<u32>, // indices that contain a `undefined`
}

mod manager {
    use super::*;

    impl<S:SymbolManager> ast::ManagerCtx for HManager<S> {
        type SymBuilder = S::Builder;
        type SymView = S::View;
        type AST = AST;
        type M = Self;
    }

    impl<S:SymbolManager> ast::Manager for HManager<S> {
        #[inline(always)]
        fn view<'a>(&'a self, t: &AST) -> HView<'a, S> {
            view_node(&self.sym_m, &self.nodes[t.0 as usize])
        }

        /// `m.mk_app(f, args)` creates the application of `f` to `args`.
        ///
        /// If the term is structurally equal to an existing term, then this
        /// ensures the exact same AST is returned ("hashconsing").
        /// If `args` is empty, return `f`.
        fn mk_app(&mut self, f: AST, args: &[AST]) -> AST {
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
        fn mk_const<U>(&mut self, s: U) -> Self::AST
            where U: std::borrow::Borrow<Self::SymView> + Into<Self::SymBuilder>
        {
            let r = self.sym_m.build(s);
            let (ast, slot) = self.allocate_id();
            *slot = NodeStored::mk_sym(r);
            ast
        }

        fn sentinel(&mut self) -> AST { AST::SENTINEL }
    }

    impl<S:SymbolManager> HManager<S> {
        // node for undefined slots, should never be exposed
        const UNDEF : NodeStored<S> =
            NodeStored { kind: Kind::Undef, data: NodeStoredData {undef: ()}, };

        /// Create a new AST manager
        pub fn new() -> Self {
            let mut tbl_app = FxHashMap::default();
            tbl_app.reserve(1_024);
            HManager {
                nodes: Vec::with_capacity(512),
                tbl_app,
                sym_m: S::new(),
                gc_alive: BitSet::new(),
                gc_stack: Vec::new(),
                recycle: Vec::new(),
            }
        }

        /// View the given AST node
        #[inline(always)]
        pub fn view(&self, ast: AST) -> HView<S> {
            view_node(&self.sym_m, &self.nodes[ast.0 as usize])
        }

        #[inline(always)]
        pub fn is_app(&self, ast: AST) -> bool {
            self.nodes[ast.0 as usize].is_app()
        }

        #[inline(always)]
        pub fn is_sym(&self, ast: AST) -> bool {
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
        fn allocate_id(&mut self) -> (AST, &mut NodeStored<S>) {
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


        /// Iterate over all the ASTs and their definition
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=(AST, HView<'a,S>)> + 'a
        {
            let sym_m = &self.sym_m;
            self.nodes.iter().enumerate()
                .filter_map(move |(i,n)| {
                    let a = AST(i as u32);
                    match n.kind {
                        Kind::Undef => None, // skip empty slot
                        _ => Some((a, view_node(sym_m, n))),
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
                if self.gc_alive.contains(&ast) {
                    continue; // subgraph already marked and traversed
                }
                self.gc_alive.add(ast);

                match view_node(&self.sym_m, &self.nodes[ast.0 as usize]) {
                    AstView::Const(_) => (),
                    AstView::App{f, args} => {
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
                    _ if self.gc_alive.contains(&AST(i as u32)) => (), // keep
                    _ => {
                        // collect
                        count += 1;
                        // remove node from `self.nodes[i]` and move it locally
                        let mut n = Self::UNDEF;
                        mem::swap(&mut self.nodes[i], &mut n);
                        // free memory of `n`, remove it from hashtable
                        unsafe { free_node(&mut self.tbl_app, &mut self.sym_m, n); }
                        self.nodes[i] = Self::UNDEF;
                        self.recycle.push(i as u32)
                    }
                }
            }
            count
        }

        fn gc_mark_root(&mut self, &ast: &AST) {
            // mark subterms transitively, using recursion stack
            let marked = self.gc_alive.contains(&ast);
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

    impl<'a, S> HManager<S>
        where S:SymbolManager,
              S::Builder : From<&'a str>,
              &'a str: std::borrow::Borrow<S::View>
    {
        /// Make a symbol node from a string
        pub fn mk_str(&mut self, s: &'a str) -> AST {
            self.mk_const(s)
        }
    }

    impl<S> HManager<S>
        where S:SymbolManager,
              S::Builder : From<String>,
              String: std::borrow::Borrow<S::View>
    {
        /// Make a symbol node from a owned string
        pub fn mk_string(&mut self, s: String) -> AST {
            self.mk_const(s)
        }
    }

    impl<S> gc::HasInternalMemory for HManager<S> where S: SymbolManager {
        fn reclaim_unused_memory(&mut self) {
            self.sym_m.reclaim_unused_memory();
            self.nodes.shrink_to_fit();
            self.tbl_app.shrink_to_fit();
            self.gc_alive.0.shrink_to_fit();
            self.gc_stack.shrink_to_fit();
            self.recycle.shrink_to_fit();
        }
    }


    /// GC for a manager's internal nodes
    impl<S> gc::GC for HManager<S> where S: SymbolManager {
        type Element = AST;

        fn mark_root(&mut self, ast: &AST) {
            self.gc_mark_root(ast)
        }

        fn collect(&mut self) -> usize {
            self.gc_collect()
        }
    }

    /// An AST can be printed, given a manager, if the symbols are pretty
    impl<S:SymbolManager> pp::Pretty1<HManager<S>> for AST
        where for<'a> &'a S::View : pp::Pretty1<S>
    {
        fn pp_with(&self, m: &HManager<S>, ctx: &mut pp::Ctx) {
            match m.view(*self) {
                AstView::Const(s) => {
                    s.pp_with(&m.sym_m, ctx);
                },
                AstView::App{f,args} if args.len() == 0 => {
                    ctx.pp(&m.pp(f)); // just f
                },
                AstView::App{f,args} => {
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

/// An implementation of `ManagerCtx` using some notion of symbol and `HManager`
pub trait HManagerCtx
    : SymbolCtx
    + ast::ManagerCtx<
        AST=AST,
        SymView=<Self as SymbolCtx>::SymView,
        SymBuilder=<Self as SymbolCtx>::SymBuilder,
        M=HManager<<Self as SymbolCtx>::SymM>>
{}

// auto impl
impl<U> HManagerCtx for U
where U: SymbolCtx,
      U: ast::ManagerCtx<
        AST=AST,
        SymView=<Self as SymbolCtx>::SymView,
        SymBuilder=<Self as SymbolCtx>::SymBuilder,
        M=HManager<<Self as SymbolCtx>::SymM>>
{}

/// A bitset whose elements are AST nodes
pub struct BitSet(::bit_set::BitSet);

mod bit_set {
    use super::*;

    impl ast::AstSet<AST> for BitSet {
        /// New bitset
        #[inline(always)]
        fn new() -> Self { BitSet(::bit_set::BitSet::new()) }

        /// Clear all bits.
        #[inline(always)]
        fn clear(&mut self) { self.0.clear() }

        #[inline(always)]
        fn contains(&self, ast: &AST) -> bool {
            self.0.contains(ast.0 as usize)
        }

        #[inline(always)]
        fn len(&self) -> usize { self.0.len () }

        #[inline]
        fn add(&mut self, ast: AST) { self.0.insert(ast.0 as usize); }

        #[inline]
        fn remove(&mut self, ast: &AST) { self.0.remove(ast.0 as usize); }
    }
    impl ast::AstDenseSet<AST> for BitSet {}

    impl<S:SymbolManager> ast::WithDenseSet<AST> for HManager<S> {
        type DenseSet = BitSet;
        fn new_dense_set() -> Self::DenseSet { BitSet::new() }
    }
}

/// A hashmap whose keys are AST nodes
pub type HashMap<V> = ast::AstHashMap<AST, V>;

/// A hashset whose keys are AST nodes
pub type HashSet = FxHashSet<AST>;


/// An AST map backed by an array, with a default value.
///
/// We assume the existence of a `sentinel` value that is used to fill the
/// vector. The sentinel should be fast to clone.
#[derive(Clone)]
pub struct DenseMap<V : Clone> {
    sentinel: V,
    mem: ::bit_set::BitSet,
    vec: Vec<V>, // mappings, but sparse (holes filled with sentinel)
    len: usize, // number of elements
}

/// implement AstDenseMap class.
mod dense_map {
    use super::*;
    use ::bit_set::BitSet;

    impl<V : Clone> ast::AstMap<AST, V> for DenseMap<V> {
        /// Access the given key
        fn get(&self, ast: &AST) -> Option<&V> {
            let i = ast.0 as usize;
            if self.mem.contains(i) {
                debug_assert!(i < self.vec.len());
                Some(&self.vec[i])
            } else {
                None
            }
        }

        /// Access the given key, return a mutable reference to its value
        fn get_mut(&mut self, ast: &AST) -> Option<&mut V> {
            let i = ast.0 as usize;
            if self.mem.contains(i) {
                debug_assert!(i < self.vec.len());
                Some(&mut self.vec[i])
            } else {
                None
            }
        }

        /// Does the map contain this key?
        fn contains(&self, ast: &AST) -> bool {
            let i = ast.0 as usize;
            self.mem.contains(i)
        }

        /// Insert a value
        fn insert(&mut self, ast: AST, v: V) {
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

        /// Remove all bindings
        fn clear(&mut self) {
            self.len = 0;
            self.vec.clear();
            self.mem.clear();
        }

        /// Remove the given key
        fn remove(&mut self, ast: &AST) {
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
        fn len(&self) -> usize {
            self.len
        }
    }

    impl<V:Clone> DenseMap<V> {
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

    impl<V : Clone> ast::AstDenseMap<AST, V> for DenseMap<V> {
        /// Create a new map with `sentinel` as an element to fill the underlying storage.
        ///
        /// It is best if `sentinel` is efficient to clone.
        fn new(sentinel: V) -> Self {
            DenseMap {sentinel, mem: BitSet::new(), vec: Vec::new(), len: 0, }
        }

        /// Access two disjoint locations, mutably.
        ///
        /// Precondition: the ASTs are distinct and in the map (panics otherwise).
        fn get2(&mut self, t1: AST, t2: AST) -> (&mut V, &mut V) {
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
    }
}

impl<S:SymbolManager,V:Clone> ast::WithDenseMap<AST, V> for HManager<S> {
    type DenseMap = DenseMap<V>;
    fn new_dense_map(sentinel: V) -> Self::DenseMap { DenseMap::new(sentinel) }
}

// check that `Manager` is just pointer-sized
#[test]
fn test_size_manager() {
    type S = StrSymbolManager;
    use std::mem;
    assert_eq!(mem::size_of::<HManager<S>>(), mem::size_of::<*const u32>());
}
