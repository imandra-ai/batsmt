
//! AST manager
//!
//! The AST manager stores AST nodes, referred to via `ID`. These nodes can
//! be used to represent sorts, terms, formulas, theory terms, etc.
//!
//! The core AST is parametrized by *symbols*, so that users can put
//! custom information in there.

use {
    std::{
        ops::{Deref,DerefMut},
        slice, u32, marker::PhantomData,
        cell::{self,RefCell,Cell},
    },
    crate::{Symbol,SymbolView,GC},
    fxhash::FxHashMap,
};

/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST(u32);

impl AST {
    /// A value of type AST. Only ever use to fill array, do not access.
    pub const SENTINEL : AST = AST(u32::MAX);
}

/// The definition of an AST node, as seen from outside
#[derive(Debug,Copy,Clone)]
pub enum View<'a, S : SymbolView<'a>> {
    Const(S::View), // symbol
    App {
        f: AST,
        args: &'a [AST],
    }
}

/// Definition of application keys
///
/// These keys are optimized so that:
/// - they don't need any allocation for "small" applications
/// - they only need to allocate one Box for "big" applications, shared between
///   the map and vector
pub(crate) struct AppStored<'a> {
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

    impl Copy for AppStored<'static> {}
    impl Clone for AppStored<'static> {
        fn clone(&self) -> Self { *self }
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
pub(crate) enum Kind { Undef, App, Sym, }

/// The definition of a node
#[derive(Clone)]
struct NodeStored<S:Symbol> {
    pub(crate) kind: Kind,
    data: node_stored::Data<S>,
}

// helper to make a view from a stored node
fn view_node<'a, S>(n: &'a NodeStored<S>) -> View<'a,S>
    where S : Symbol
{
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

mod node_stored {
    use super::*;

    #[derive(Copy,Clone)]
    pub(crate) union Data<SPtr : Copy> {
        pub undef: (),
        pub app: AppStored<'static>,
        pub sym: SPtr, // raw pointer to a symbol
    }

    impl<S:Symbol> NodeStored<S> {
        /// Make a constant node from a symbol
        pub fn mk_sym(sym: S::Owned) -> Self {
            let ptr = unsafe { S::to_ptr(sym) };
            NodeStored {data: Data{sym: ptr}, kind: Kind::Sym }
        }
        pub fn mk_app(app: AppStored<'static>) -> Self {
            NodeStored {kind: Kind::App, data: Data { app }}
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
    tbl: &mut FxHashMap<AppStored<'static>, AST>, mut n: NodeStored<S>)
{
    if n.kind() == Kind::App {
        let app = n.as_app();
        // remove from table
        tbl.remove_entry(&app);
    }
    n.free();
}

/// The internal state of the manager.
///
/// This state can be obtained via `Manager::get` or `Manager::get_mut`,
/// and provides most of the useful functions to manipulate ASTs
pub struct ManagerCell<S:Symbol> {
    nodes: Vec<NodeStored<S>>,
    tbl_app: FxHashMap<AppStored<'static>, AST>, // for hashconsing
    // TODO: use some bits of nodes[i].kind (a u8) for this?
    gc_alive: BitSet, // for GC
    gc_stack: Vec<AST>, // temporary vector for GC marking
    recycle: Vec<u32>, // indices that contain a `undefined`
}

// NOTE: similar to the PIMPL pattern in C++.
/// The AST manager, responsible for storing and creating AST nodes
///
/// The manager is parametrized by the type of symbols used.
/// It is not shareable among threads.
/// ```compile_fail
/// use batsmt_core::{ast,Symbol};
/// struct Foo<S:Symbol>(ast::Manager<S>);
/// fn foo<A:Sync>(a: &A) {};
/// fn bar<S:Symbol>(x: &Foo<S>) { foo(x) }
/// ```
pub struct Manager<S:Symbol>(*mut ManagerCellRC<S>);

// a wrapped managerCell, with a refcount
struct ManagerCellRC<S:Symbol> {
    rc: Cell<u16>,
    cell: RefCell<ManagerCell<S>>,
}

/// A borrowed reference to the AST manager.
///
/// It has a limited lifetime (`'a`) but provides access to views of AST symbols
pub struct ManagerRef<'a, S:Symbol>(cell::Ref<'a, ManagerCell<S>>);

/// A borrowed mutable reference to the AST manager.
///
/// It has a limited lifetime (`'a`) and cannot be aliased.
pub struct ManagerRefMut<'a, S:Symbol>(cell::RefMut<'a, ManagerCell<S>>);

mod manager {
    use super::*;

    impl<S:Symbol> ManagerCell<S> {
        // node for undefined slots, should never be exposed
        const UNDEF : NodeStored<S> =
            NodeStored { kind: Kind::Undef, data: node_stored::Data {undef: ()}, };

        /// Create a new AST manager
        pub(crate) fn new() -> Self {
            let mut tbl_app = FxHashMap::default();
            tbl_app.reserve(1_024);
            ManagerCell {
                nodes: Vec::with_capacity(512),
                tbl_app,
                gc_alive: BitSet::new(),
                gc_stack: Vec::new(),
                recycle: Vec::new(),
            }
        }

        /// View the given symbol
        #[inline(always)]
        pub fn view(&self, ast: AST) -> View<S> {
            view_node(&self.nodes[ast.0 as usize])
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

        /// `m.mk_app(f, args)` creates the application of `f` to `args`.
        ///
        /// If the term is structurally equal to an existing term, then this
        /// ensures the exact same AST is returned ("hashconsing")
        pub fn mk_app(&mut self, f: AST, args: &[AST]) -> AST {
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
        pub fn mk_sym(&mut self, s: S::Owned) -> AST {
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

        fn gc_mark_root(&mut self, &ast: &AST) {
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

    impl<S> ManagerCell<S> where S:Symbol, S::Owned : for<'a> From<&'a str> {
        /// Make a symbol node from a string
        pub fn mk_str(&mut self, s: &str) -> AST {
            let sym: S::Owned = s.into();
            self.mk_sym(sym)
        }
    }

    impl<S> ManagerCell<S> where S:Symbol, S::Owned : From<String> {
        /// Make a symbol node from a owned string
        pub fn mk_string(&mut self, s: String) -> AST {
            let sym: S::Owned = s.into();
            self.mk_sym(sym)
        }
    }

    impl<'a, S:Symbol> Deref for ManagerRef<'a, S> {
        type Target = ManagerCell<S>;
        fn deref(&self) -> &Self::Target { self.0.deref() }
    }

    impl<'a, S:Symbol> Deref for ManagerRefMut<'a, S> {
        type Target = ManagerCell<S>;
        fn deref(&self) -> &Self::Target { self.0.deref() }
    }

    impl<'a, S:Symbol> DerefMut for ManagerRefMut<'a, S> {
        fn deref_mut(&mut self) -> &mut Self::Target { self.0.deref_mut() }
    }

    /// The public interface of the manager.
    ///
    /// A `Manager<S>` is a shared pointer to the actual data.
    /// Use `get` or `get_mut` to gain access to the internals.
    impl<S:Symbol> Manager<S> {
        /// Temporary reference
        #[inline(always)]
        pub fn get<'a>(&'a self) -> ManagerRef<'a, S> {
            let rc : &RefCell<_> = unsafe{ &(*self.0).cell };
            let r = rc.borrow();
            ManagerRef(r)
        }

        /// Temporary mutable reference
        #[inline(always)]
        pub fn get_mut<'a>(&'a self) -> ManagerRefMut<'a, S> {
            // interior mutability, here we come!
            let rc : &RefCell<_> = unsafe { &(*self.0).cell };
            let r = rc.borrow_mut();
            ManagerRefMut(r)
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
            // allocate on heap
            let b = Box::new(ManagerCellRC {
                rc: Cell::new(1),
                cell: RefCell::new(m),
            });
            Manager(Box::into_raw(b))
        }
    }

    impl<S:Symbol> Clone for Manager<S> {
        // clone and increment refcount
        fn clone(&self) -> Self {
            let rc = unsafe { &mut (*self.0).rc };
            rc.set(rc.get() + 1);
            Manager(self.0)
        }
    }

    impl<S:Symbol> Drop for Manager<S> {
        // clone and increment refcount
        fn drop(&mut self) {
            let dead = {
                let rc = unsafe { &mut (*self.0).rc };
                let n = rc.get();
                debug_assert!(n > 0);
                rc.set(n - 1);
                n-1 == 0
            };
            if dead {
                let b: Box<ManagerCellRC<_>> = unsafe { Box::from_raw(self.0) };
                drop(b)
            }
        }
    }

    /// GC for a manager's internal nodes
    impl<S> GC for Manager<S> where S: Symbol {
        type Element = AST;

        fn mark_root(&mut self, ast: &AST) {
            self.get_mut().gc_mark_root(ast)
        }

        fn collect(&mut self) -> usize {
            self.get_mut().gc_collect()
        }
    }

    impl<S> Manager<S> where S:Symbol, S::Owned : for<'a> From<&'a str> {
        /// Make a symbol node from a string
        pub fn mk_str(&self, s: &str) -> AST { self.get_mut().mk_str(s) }
    }

    impl<S> Manager<S> where S:Symbol, S::Owned : From<String> {
        /// Make a symbol node from a owned string
        pub fn mk_string(&self, s: String) -> AST { self.get_mut().mk_string(s) }
    }
}

/// A bitset whose elements are AST nodes
pub struct BitSet(::bit_set::BitSet);

mod bit_set {
    use super::*;
    use std::ops::Deref;

    impl BitSet {
        /// New bitset
        #[inline(always)]
        pub fn new() -> Self { BitSet(::bit_set::BitSet::new()) }

        /// Clear all bits
        #[inline(always)]
        pub fn clear(&mut self) { self.0.clear() }

        #[inline(always)]
        pub fn len(&self) -> usize { self.0.len () }

        #[inline(always)]
        pub fn get(&self, ast: AST) -> bool {
            self.0.contains(ast.0 as usize)
        }

        #[inline]
        pub fn add(&mut self, ast: AST) { self.0.insert(ast.0 as usize); }

        #[inline]
        pub fn remove(&mut self, ast: AST) { self.0.remove(ast.0 as usize); }

        pub fn add_slice(&mut self, arr: &[AST]) {
            for &ast in arr { self.add(ast) }
        }

        /// Add all the ASTs in the given iterator
        pub fn add_iter<Q, I>(&mut self, iter:I)
            where I: Iterator<Item=Q>, Q: Deref<Target=AST>
        {
            for ast in iter {
                self.add(*ast)
            }
        }
    }
}

/// A hashmap whose keys are AST nodes
pub type HashMap<V> = FxHashMap<AST,V>;

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
        pub fn get(&self, ast: AST) -> Option<&V> {
            let i = ast.0 as usize;
            if self.mem.contains(i) {
                debug_assert!(i < self.vec.len());
                Some(&self.vec[i])
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

// check that `Manager` is just pointer-sized
#[test]
fn test_size_manager() {
    use crate::StrSymbol as S;
    use std::mem;
    assert_eq!(mem::size_of::<Manager<S>>(), mem::size_of::<*const u32>());
}
