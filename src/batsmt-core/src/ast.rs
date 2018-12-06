
//! AST manager
//!
//! The AST manager stores AST nodes, referred to via `ID`. These nodes can
//! be used to represent sorts, terms, formulas, theory terms, etc.

use std::u32;
use std::slice;
use super::{Symbol,GC};
use fxhash::FxHashMap;

/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST(u32);

impl AST {
    /// A value of type AST. Only ever use to fill array, do not access.
    pub const SENTINEL : AST = AST(u32::MAX);
}

/// The definition of an AST node, as seen from outside
#[derive(Debug,Copy,Clone)]
pub enum View<'a> {
    Const(Symbol<'a>),
    App {
        f: AST,
        args: &'a [AST],
    }
}

// Definition of application keys
//
// These keys are optimized so that:
// - they don't need any allocation for "small" applications
// - they only need to allocate one Box for "big" applications, shared between
//   the map and vector
mod app_stored {
    use super::*;
    use std::marker::PhantomData;

    // Number of arguments for a "small" term application
    const N_SMALL_APP : usize = 3;

    #[derive(Copy,Clone)]
    union ArrOrVec<T : Copy> {
        arr: [T; N_SMALL_APP],
        ptr: * const T, // will be shared between vec and hashmap
    }

    // Main type
    pub(crate) struct T<'a> {
        f: AST,
        len: u16,
        args: ArrOrVec<AST>,
        phantom: PhantomData<&'a ()>,
    }

    fn check_len(len: usize) {
        use std::u16;
        if len > u16::MAX as usize {
            panic!("cannot make an AST application of length {}", len);
        }
    }

    impl T<'static> {
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
            let r = T {
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

    impl<'a> T<'a> {
        #[inline(always)]
        pub fn f(&self) -> AST { self.f }

        #[inline(always)]
        pub fn args<'b: 'a>(&'b self) -> &'b [AST] {
            let len = self.len as usize;
            if len <= N_SMALL_APP {
                unsafe {& self.args.arr[..len]}
            } else {
                unsafe {slice::from_raw_parts(self.args.ptr, len)}
            }
        }

        // Temporary-lived key, borrowing the given slice
        pub fn mk_ref(f: AST, args: &'a [AST]) -> Self {
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
            let r = T {
                f, len: len as u16, args: new_args,
                phantom: PhantomData::default(),
            };
            debug_assert_eq!(r.args(), args, "expected {:?} got {:?}", args, r.args());
            r
        }

        pub fn to_owned(self) -> T<'static> {
            T::new(self.f, self.args())
        }
    }

    impl Copy for T<'static> {}
    impl Clone for T<'static> {
        fn clone(&self) -> Self { *self }
    }

    impl<'a> Eq for T<'a> {}
    impl<'a> PartialEq for T<'a> {
        fn eq(&self, other: &T<'a>) -> bool {
            self.f == other.f && self.args() == other.args()
        }
    }

    use std::hash::{Hash,Hasher};

    impl<'a> Hash for T<'a> {
        fn hash<H:Hasher>(&self, h: &mut H) {
            self.f.hash(h);
            self.args().hash(h)
        }
    }

    use std::fmt::{Debug,self};

    impl<'a> Debug for T<'a> {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            write!(fmt, "({:?} {:?})", self.f, self.args())
        }
    }
}

// The kind of object stored in a given slot
#[repr(u8)]
#[derive(Copy,Clone,Debug,Eq,PartialEq,Hash)]
pub(crate) enum Kind { Undef, App, Str, Custom, }

mod node_stored {
    use super::*;
    use symbol::Custom;

    // One node in the main vector
    #[derive(Clone)]
    pub(crate) struct T {
        pub kind: Kind,
        data: Data,
    }

    #[derive(Copy,Clone)]
    union Data {
        undef: (),
        app: app_stored::T<'static>,
        str: (*const u8, usize), // owned string
        custom: *const Custom,
    }

    // Constant for undefined
    pub(crate) const UNDEF : T = T { kind: Kind::Undef, data: Data {undef: ()}, };

    impl T {
        pub fn from_string(s:String) -> Self {
            use std::mem;
            let ptr = s.as_ptr();
            let len = s.as_bytes().len();
            mem::forget(s);
            let data = Data { str: (ptr, len) };
            T {kind: Kind::Str, data }
        }
        pub fn mk_str(s: &str) -> Self {
            let s = s.to_string();
            T::from_string(s)
        }
        pub fn mk_app(app: app_stored::T<'static>) -> Self {
            T {kind: Kind::App, data: Data { app }}
        }

        #[inline(always)]
        pub fn kind(&self) -> Kind { self.kind }
        #[inline(always)]
        pub fn is_undef(&self) -> bool { self.kind() == Kind::Undef }
        #[inline(always)]
        pub fn is_app(&self) -> bool { self.kind() == Kind::App }
        #[inline(always)]
        pub fn is_sym(&self) -> bool { let k = self.kind(); k == Kind::Str || k == Kind::Custom  }

        pub unsafe fn as_app(&self) -> &app_stored::T<'static> {
            debug_assert!(self.kind() == Kind::App);
            &self.data.app
        }

        // view as a string symbol
        pub unsafe fn as_str(&self) -> &str {
            debug_assert!(self.kind() == Kind::Str);
            use std::str;
            let (ptr, len) = self.data.str;
            let slice = std::slice::from_raw_parts(ptr, len);
            &mut str::from_utf8_unchecked(slice)
        }

        pub unsafe fn as_custom(&self) -> &Custom {
            debug_assert!(self.kind() == Kind::Custom);
            &* self.data.custom
        }

        /// release resources
        pub unsafe fn free(&mut self) {
            match self.kind {
                Kind::Undef => (),
                Kind::App => self.data.app.free(),
                Kind::Str => {
                    let (ptr, len) = self.data.str;
                    let ptr = ptr as *mut u8;
                    let v = Vec::from_raw_parts(ptr, len, len);
                    drop(v)
                },
                Kind::Custom => {
                    let ptr = self.data.custom as *mut Custom;
                    let b = Box::from_raw(ptr);
                    drop(b)
                }
            }
        }
    }
}

// helper to make a view from a stored node
fn view_node<'a>(ast: AST, n: &'a node_stored::T) -> View<'a> {
    match n.kind() {
        Kind::App => {
            let k = unsafe {n.as_app()};
            View::App {f: k.f(), args: k.args()}
        },
        Kind::Str => View::Const(Symbol::Str{name: unsafe {n.as_str()}}),
        Kind::Custom => View::Const(Symbol::Custom{content: unsafe {n.as_custom()}}),
        Kind::Undef => panic!("cannot access undefined AST {:?}", ast),
    }
}

// free memory for this node, including its hashmap entry if any
unsafe fn free_node(tbl: &mut FxHashMap<app_stored::T<'static>, AST>, mut n: node_stored::T) {
    if n.kind() == Kind::App {
        let app = n.as_app();
        // remove from table
        tbl.remove_entry(&app);
    }
    n.free();
}

/// The AST manager, responsible for storing and creating AST nodes
pub struct Manager {
    nodes: Vec<node_stored::T>,
    tbl_app: FxHashMap<app_stored::T<'static>, AST>, // for hashconsing
    // TODO: use some bits of nodes[i].kind (a u8) for this?
    gc_alive: BitSet, // for GC
    gc_stack: Vec<AST>, // temporary vector for GC marking
    recycle: Vec<u32>, // indices that contain a `undefined`
}

impl Manager {
    /// Create a new AST manager
    pub fn new() -> Self {
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

    /// View the definition of an AST node
    #[inline]
    pub fn view(&self, ast: AST) -> View {
        let n = &self.nodes[ast.0 as usize];
        view_node(ast, n)
    }

    /// Number of terms
    pub fn n_terms(&self) -> usize {
        let nlen = self.nodes.len();
        let rlen = self.recycle.len();
        debug_assert!(nlen >= rlen);
        nlen - rlen
    }

    // allocate a new AST ID, and return the slot it should live in
    fn allocate_id(&mut self) -> (AST, &mut node_stored::T) {
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
                self.nodes.push(node_stored::UNDEF);
                let slot = &mut self.nodes[n];
                (AST(n as u32), slot)
            }
        }

    }

    /// Make a named symbol.
    ///
    /// Note that calling this function twice with the same string
    /// will result in two distinct symbols (as if the second one
    /// was shadowing the first). Use an auxiliary hashtable if
    /// you want sharing.
    pub fn mk_const(&mut self, s: &str) -> AST {
        let (ast, slot) = self.allocate_id();
        *slot = node_stored::T::mk_str(s);
        ast
    }

    /// `m.mk_app(f, args)` creates the application of `f` to `args`.
    ///
    /// If the term is structurally equal to an existing term, then this
    /// ensures the exact same AST is returned ("hashconsing")
    pub fn mk_app(&mut self, f: AST, args: &[AST]) -> AST {
        let k = app_stored::T::mk_ref(f, args);

        // borrow multiple fields
        let nodes = &mut self.nodes;
        let tbl_app = &mut self.tbl_app;
        //let Manager {ref mut apps, ref mut tbl_app,..} = self;

        match tbl_app.get(&k) {
            Some(&a) => a, // fast path
            None => {
                // insert
                let n = nodes.len();
                let ast = AST(n as u32);
                // make 2 owned copies of the key
                let k1 = k.to_owned();
                let k2 = k1.clone();
                nodes.push(node_stored::T::mk_app(k1));
                tbl_app.insert(k2, ast);
                // return AST
                ast
            }
        }
    }

    /// Iterate over all ASTs in the manager, along with their view
    pub fn iter<'a>(&'a self) -> impl Iterator<Item=(AST, View<'a>)> + 'a {
        self.nodes.iter().enumerate()
            .filter_map(move |(i,n)| {
                let a = AST(i as u32);
                match n.kind {
                    Kind::Undef => None, // skip empty slot
                    _ => Some((a, view_node(a, n))),
                }
            })
    }

    /// Iterate on the ASTs contained in this manager, without their view
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
        //let gc_stack = &mut self.gc_stack;
        //let gc_alive = &mut self.gc_alive;
        while let Some(ast) = self.gc_stack.pop() {
            if self.gc_alive.get(ast) {
                continue; // subgraph already marked and traversed
            }
            self.gc_alive.add(ast);

            match view_node(ast, &self.nodes[ast.0 as usize]) {
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
                    let mut n = node_stored::UNDEF;
                    mem::swap(&mut self.nodes[i], &mut n);
                    // free memory of `n`, remove it from hashtable
                    unsafe { free_node(&mut self.tbl_app, n); }
                    self.nodes[i] = node_stored::UNDEF;
                    self.recycle.push(i as u32)
                }
            }
        }
        count
    }
}

/// Iterator over ASTs
impl GC for Manager {
    type Element = AST;

    fn mark_root(&mut self, &ast: &AST) {
        // mark subterms transitively, using recursion stack
        let marked = self.gc_alive.get(ast);
        if !marked {
            self.gc_stack.push(ast);
            self.gc_traverse_and_mark();
        }
    }

    fn collect(&mut self) -> usize {
        let n = self.gc_retain_roots();
        self.gc_alive.clear();
        n
    }
}

mod bit_set {
    use super::*;
    use std::ops::Deref;
    use bit_set::BitSet;

    pub struct T(BitSet);

    impl T {
        /// New bitset
        #[inline(always)]
        pub fn new() -> Self { T(BitSet::new()) }

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

/// A bitset whose elements are AST nodes
pub type BitSet = bit_set::T;

/// A hashmap whose keys are AST nodes
pub type HashMap<V> = FxHashMap<AST,V>;

mod dense_map {
    use super::*;
    use bit_set::BitSet;

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
