
//! AST manager
//!
//! The AST manager stores AST nodes, referred to via `ID`. These nodes can
//! be used to represent sorts, terms, formulas, theory terms, etc.
//!
//! The core AST is parametrized by *symbols*, so that users can put
//! custom information in there.

use {
    std::{
        ops::{Deref,DerefMut}, fmt,
        slice, u32, marker::PhantomData,
    },
    crate::{
        Symbol,SymbolView,GC,
        Shared,SharedRef,SharedRefMut,
    },
    fxhash::{FxHashMap,FxHashSet},
    batsmt_pretty as pp,
};

/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST(u32);

impl AST {
    /// A value of type AST. Only ever use to fill array, do not access.
    pub const SENTINEL : AST = AST(u32::MAX);
}

/// The definition of an AST node, as seen from outside.
///
/// This view automatically gives a view of the symbols as well.
#[derive(Debug,Copy,Clone)]
pub enum View<'a, S : SymbolView<'a>> {
    Const(S::View), // symbol view
    App {
        f: AST,
        args: &'a [AST],
    }
}

/// Temporary view of a mapped term
pub enum MapView<'a, R> {
    Const, // the AST itself contains the symbol
    App{f: &'a R, args: &'a [R]},
}

// FIXME: remove this, it's unsafe (gc would invalidate)
/// The definition of an AST node, as seen from outside.
///
/// This view gives access to the symbol itself.
#[derive(Debug,Copy,Clone)]
pub enum ViewSym<'a, S : Symbol> {
    Const(S), // symbol itself
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
#[derive(Clone)]
pub struct Manager<S:Symbol>(Shared<ManagerCell<S>>);

/// A borrowed reference to the AST manager.
///
/// It has a limited lifetime (`'a`) but provides access to views of AST symbols
pub struct ManagerRef<'a, S:Symbol>(SharedRef<'a, ManagerCell<S>>);

/// A borrowed mutable reference to the AST manager.
///
/// It has a limited lifetime (`'a`) and cannot be aliased.
pub struct ManagerRefMut<'a, S:Symbol>(SharedRefMut<'a, ManagerCell<S>>);

/// used for printing
struct WithManager<'a, S:Symbol, T>(&'a Manager<S>, T);

/// Objects that can be pretty-printed if paired with a manager
pub trait PrettyM {
    fn pp_m<S:Symbol>(&self, m: &Manager<S>, ctx: &mut pp::Ctx);
}

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

        /// View the given AST node
        #[inline(always)]
        pub fn view(&self, ast: AST) -> View<S> {
            view_node(&self.nodes[ast.0 as usize])
        }

        /// View the given AST node
        #[inline(always)]
        pub fn view_sym(&self, ast: AST) -> ViewSym<S> {
            view_sym_node(&self.nodes[ast.0 as usize])
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
        /// ensures the exact same AST is returned ("hashconsing").
        /// If `args` is empty, return `f`.
        pub fn mk_app(&mut self, f: AST, args: &[AST]) -> AST {
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
        pub fn iter_dag<F>(&self, t: AST, f: F) where F: FnMut(AST) {
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
            self.iter_dag(t, |_| { n += 1 });
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

    // ### Pretty printing

    impl<S:Symbol> Manager<S> {
        /// Pretty-printable version of the given object
        pub fn pp<'a, T:PrettyM+'a>(&'a self, x:T) -> impl pp::Pretty+fmt::Display+fmt::Debug+'a {
            WithManager(&self, x)
        }
    }

    impl<'a, S:Symbol, T:PrettyM> pp::Pretty for WithManager<'a,S,T> {
        fn pp(&self, ctx: &mut pp::Ctx) {
            let WithManager(m,t) = self;
            t.pp_m(m, ctx)
        }
    }

    impl<'a, S:Symbol, T:PrettyM> fmt::Display for WithManager<'a,S,T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            pp::Pretty::pp_fmt(&self,out, false)
        }
    }
    impl<'a, S:Symbol, T:PrettyM> fmt::Debug for WithManager<'a,S,T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            pp::Pretty::pp_fmt(&self,out, true)
        }
    }

    impl<'a, T:PrettyM> PrettyM for &'a T {
        fn pp_m<S:Symbol>(&self, m: &Manager<S>, ctx: &mut pp::Ctx) { (*self).pp_m(m,ctx) }
    }

    /// An AST can be printed, given a manager, if the symbols are pretty
    impl PrettyM for AST {
        fn pp_m<S:Symbol>(&self, m: &Manager<S>, ctx: &mut pp::Ctx) {
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

mod view {
    use super::*;

    impl<'a,S:Symbol> View<'a, S> {
        pub fn is_app(&self) -> bool { match self { View::App{..} => true, _ => false } }
        pub fn is_const(&self) -> bool { match self { View::Const(..) => true, _ => false } }

        /// Iterate over the immediate subterms of this view.
        pub fn subterms(&self) -> impl Iterator<Item=AST> + 'a {
            match self {
                View::Const(_) => ViewIter::Nil,
                View::App{f, args} => ViewIter::App(*f, args),
            }
        }
    }

    // custom iterator oversubterms
    enum ViewIter<'a> {
        Nil,
        Args(&'a [AST], usize),
        App(AST, &'a [AST]),
    }

    // custom iterator
    impl<'a> Iterator for ViewIter<'a> {
        type Item = AST;
        fn next(&mut self) -> Option<Self::Item> {
            match self {
                ViewIter::Nil => None,
                ViewIter::App(f,args) => {
                    let f = *f;
                    *self = ViewIter::Args(args,0);
                    Some(f)
                },
                ViewIter::Args(args, n) => {
                    if *n == args.len() {
                        None
                    } else {
                        let t = args[*n];
                        *n += 1;
                        Some(t)
                    }
                }
            }
        }
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

/// A hashset whose keys are AST nodes
pub type HashSet = FxHashSet<AST>;

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

/// Iterate over sub-terms.
///
/// Iteration over sub-terms, without repetition (sharing means a common
/// subterm will be traversed only once).
/// The order in which terms are traversed is not specified.
pub mod iter_dag {
    use super::*;

    #[derive(Clone)]
    pub struct State<S:Symbol> {
        m: Manager<S>,
        st: State0,
    }

    // internal structure, separate from `m`
    #[derive(Clone)]
    struct State0 {
        st: Vec<AST>,
        seen: HashSet,
    }

    impl<S> State<S> where S: Symbol {
        /// New state
        pub fn new(m: &Manager<S>) -> Self {
            let m = m.clone();
            State { m, st: State0::new(), }
        }

        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `f` is the function to call once on every subterm
        pub fn iter<F>(&mut self, t: AST, mut f: F) where F: FnMut(AST) {
            if self.st.seen.len() > 0 && self.st.seen.contains(&t) { return }

            self.st.push(t);
            while let Some(t) = self.st.st.pop() {
                if self.st.seen.contains(&t) {
                    continue
                } else {
                    self.st.seen.insert(t);
                    f(t); // process `t`

                    match self.m.get().view(t) {
                        View::Const(_) => (),
                        View::App{f,args} => {
                            self.st.push(f);
                            for a in args.iter() { self.st.push(*a) }
                        },
                    }
                }
            }
        }

        /// Clear state, forgetting all the subterms seen so far.
        pub fn clear(&mut self) {
            self.st.st.clear();
            self.st.seen.clear();
        }
    }

    impl State0 {
        fn new() -> Self {
            Self {seen: HashSet::default(), st: Vec::new(), }
        }

        /// local conditional push
        fn push(&mut self, t:AST) {
            if ! self.seen.contains(&t) {
                self.st.push(t)
            }
        }
    }

    impl<S:Symbol> fmt::Debug for State<S> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "iter_dag.state")
        }
    }
}

/// Iterate over sub-terms, in suffix order.
///
/// Each sub-term is touched once, and parent terms are processed *after*
/// their subterms.
pub mod iter_suffix {
    use super::*;

    #[derive(Clone)]
    pub struct State<S:Symbol> {
        m: Manager<S>,
        st: State0,
    }

    // flag: are we entering the term, or exiting it?
    #[repr(u8)]
    #[derive(Copy,Clone,PartialEq,Eq,Debug)]
    enum EE { Enter, Exit }

    // internal structure, separate from `m`
    #[derive(Clone)]
    struct State0 {
        st: Vec<(EE,AST)>,
        seen: HashSet,
    }

    impl<S> State<S> where S: Symbol {
        /// New state
        pub fn new(m: &Manager<S>) -> Self {
            let m = m.clone();
            State { m, st: State0::new(), }
        }

        /// Iterate over the given AST `t`, calling a function on every subterm once.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `fenter` is called _before_ processing a subterm.
        ///    If it returns `true`, the term is explored.
        /// - `fexit` is the function to call once on every subterm that `fenter` approved.
        pub fn iter<Ctx,F1,F2>(
            &mut self, t: AST, ctx: &mut Ctx, mut fenter: F1, mut fexit: F2
        )
            where F1: FnMut(&mut Ctx, AST)->bool, F2: FnMut(&mut Ctx, AST)
        {
            if self.st.seen.len() > 0 && self.st.seen.contains(&t) { return }

            self.st.push_enter(t);
            while let Some((ee,t)) = self.st.st.pop() {
                if ee == EE::Exit {
                    fexit(ctx, t); // process `t`
                } else if self.st.seen.contains(&t) {
                    continue
                } else {
                    debug_assert_eq!(ee, EE::Enter);
                    self.st.seen.insert(t);

                    if !fenter(ctx, t) {
                        continue // do not actually explore this
                    }

                    // exit `t` after processing subterms
                    self.st.push_exit(t);

                    // explore subterms first
                    match self.m.get().view(t) {
                        View::Const(_) => (),
                        View::App{f,args} => {
                            self.st.push_enter(f);
                            for &a in args.iter() { self.st.push_enter(a) }
                        },
                    }
                }
            }
        }

        /// Clear state, forgetting all the subterms seen so far.
        pub fn clear(&mut self) {
            self.st.st.clear();
            self.st.seen.clear();
        }
    }

    impl State0 {
        fn new() -> Self {
            Self {seen: HashSet::default(), st: Vec::new(), }
        }

        #[inline(always)]
        fn push_enter(&mut self, t:AST) { self.st.push((EE::Enter,t)); }

        #[inline(always)]
        fn push_exit(&mut self, t: AST) { self.st.push((EE::Exit,t)) }
    }

    impl<S:Symbol> fmt::Debug for State<S> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "iter_suffix.state")
        }
    }
}

/// Map sub-terms to arbitrary values.
///
/// Iteration over sub-terms, without repetition (sharing means a common
/// subterm will be traversed only once).
pub mod map_dag {
    use super::*;

    #[derive(Clone)]
    pub struct State<S:Symbol, R: Clone> {
        m: Manager<S>,
        st: State0<R>,
    }

    // internal structure, separate from `m`
    #[derive(Clone)]
    struct State0<R> {
        tasks: Vec<Task>,
        res: Vec<R>, // intermediate results
        cache: HashMap<R>, // cached values
        args: Vec<R>, // for creating `MapView`
    }

    #[derive(Clone)]
    enum Task {
        // must be an application of `n` arguments.
        // Pops `n+1` from `res`, pushes one value onto `res`.
        Exit(AST),
        Enter(AST), // will eventually push one value onto `res`
    }

    impl<S,R> State<S,R> where S: Symbol, R: Clone {
        /// New state
        pub fn new(m: &Manager<S>) -> Self {
            let m = m.clone();
            State {m, st: State0::new(), }
        }

        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// `f` is passed:
        /// - the manager itself
        /// - the original subterm
        /// - a view of the original subterm where its own immediate subterms
        ///   have been transformed by `f` already
        pub fn map<F>(&mut self, t: AST, mut f: F) -> R
            where F: for<'a> FnMut(&Manager<S>, AST, MapView<R>) -> R
        {
            self.st.tasks.push(Task::Enter(t));
            let m2 = self.m.clone();
            while let Some(task) = self.st.tasks.pop() {
                match task {
                    Task::Enter(t) => {
                        match self.st.cache.get(&t) {
                            Some(u) => self.st.res.push(u.clone()), // cached
                            None => {
                                // explore subterms first, then schedule a call for `f`
                                match self.m.get().view(t) {
                                    View::Const(_) => {
                                        let view = MapView::Const;
                                        let r = f(&m2, t, view);
                                        // put into cache and return immediately
                                        self.st.cache.insert(t, r.clone());
                                        self.st.res.push(r);
                                    }
                                    View::App{f, args} => {
                                        // process `f` and `args` before exiting `t`
                                        self.st.tasks.push(Task::Exit(t));
                                        self.st.tasks.push(Task::Enter(f));
                                        for &u in args.iter() {
                                            self.st.tasks.push(Task::Enter(u));
                                        }
                                    }
                                }
                            },
                        }
                    },
                    Task::Exit(t) => {
                        let n = match self.m.get().view(t) {
                            View::Const(_) => unreachable!(),
                            View::App{f:_, args} => args.len(),
                        };
                        // move arguments from stack to `st.args`
                        self.st.args.clear();
                        let head = self.st.res.pop().unwrap();
                        for _i in 0..n {
                            self.st.args.push(self.st.res.pop().unwrap());
                        }
                        let view = MapView::App{f: &head, args: &self.st.args};
                        let r = f(&self.m, t, view);
                        self.st.cache.insert(t, r.clone()); // save in cache
                        self.st.res.push(r); // return result
                    },
                }
            }

            debug_assert_eq!(self.st.res.len(), 1);
            self.st.res.pop().unwrap()
        }
    }

    impl<R> State0<R> {
        fn new() -> Self {
            Self {
                cache: HashMap::default(), tasks: vec!(),
                res: vec!(), args: vec!(),
            }
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
