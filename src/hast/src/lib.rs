
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
    batsmt_core::{
        ast::{Manager, },
        ast_u32::{self, DenseSet, }, gc, AstView, },
    fxhash::{FxHashMap},
    batsmt_pretty as pp,
};

pub use {
    crate::symbol::{ SymbolCtx, SymbolManager, str::StrManager as StrSymbolManager, }
};

/// Use the `u32` AST.
pub use batsmt_core::ast_u32::AST;

pub type HView<'a, S> = AstView<'a, &'a <S as SymbolCtx>::View, AST>;

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
                    let mut arr = [AST::SENTINEL; N_SMALL_APP];
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
                    let mut arr = [AST::SENTINEL; N_SMALL_APP];
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
#[inline]
fn view_node<'a, S>(sym: &'a S, n: &'a NodeStored<S>)
    -> HView<'a, S> where S : SymbolManager
{
    match n.kind() {
        Kind::App => {
            let k = unsafe {n.as_app()};
            AstView::App {f: &k.f, args: k.args()}
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
    gc_alive: ast_u32::DenseSet, // for GC
    gc_stack: Vec<AST>, // temporary vector for GC marking
    recycle: Vec<u32>, // indices that contain a `undefined`
}

mod manager {
    use {
        super::*, batsmt_core::ast::{ Manager, AstSet, },
    };

    impl<S:SymbolManager> Manager for HManager<S> {
        type SymBuilder = S::Builder;
        type SymView = S::View;
        type AST = AST;

        #[inline(always)]
        fn view<'a>(&'a self, t: &AST) -> HView<'a, S> {
            view_node(&self.sym_m, &self.nodes[t.idx() as usize])
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
                    let ast = ast_u32::manager_util::ast_from_u32(n as u32);
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
                gc_alive: DenseSet::new(),
                gc_stack: Vec::new(),
                recycle: Vec::new(),
            }
        }

        /// View the given AST node
        #[inline(always)]
        pub fn view(&self, ast: AST) -> HView<S> {
            view_node(&self.sym_m, &self.nodes[ast.idx() as usize])
        }

        #[inline(always)]
        pub fn is_app(&self, ast: AST) -> bool {
            self.nodes[ast.idx() as usize].is_app()
        }

        #[inline(always)]
        pub fn is_sym(&self, ast: AST) -> bool {
            self.nodes[ast.idx() as usize].is_sym()
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
                    let ast = ast_u32::manager_util::ast_from_u32(n);
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
                    (ast_u32::manager_util::ast_from_u32(n as u32), slot)
                }
            }
        }


        /// Iterate over all the ASTs and their definition
        pub fn iter<'a>(&'a self) -> impl Iterator<Item=(AST, HView<'a,S>)> + 'a
        {
            let sym_m = &self.sym_m;
            self.nodes.iter().enumerate()
                .filter_map(move |(i,n)| {
                    let a = ast_u32::manager_util::ast_from_u32(i as u32);
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
                    let a = ast_u32::manager_util::ast_from_u32(i as u32);
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

                match view_node(&self.sym_m, &self.nodes[ast.idx() as usize]) {
                    AstView::Const(_) => (),
                    AstView::App{f, args} => {
                        // explore subterms, too
                        self.gc_stack.push(*f);
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
                    _ if self.gc_alive.contains(
                        &ast_u32::manager_util::ast_from_u32(i as u32)) => (), // keep
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
            self.gc_alive.shrink_to_fit();
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
    impl<S:SymbolManager> pp::Pretty1<AST> for HManager<S> {
        fn pp1_into(&self, t: &AST, ctx: &mut pp::Ctx) {
            match self.view(*t) {
                AstView::Const(s) => {
                    self.sym_m.pp1_into(&s, ctx);
                },
                AstView::App{f,args} if args.len() == 0 => {
                    self.pp1_into(&f, ctx); // just f
                },
                AstView::App{f,args} => {
                    ctx.sexp(|ctx| {
                        self.pp1_into(&f, ctx);
                        ctx.space();
                        ctx.iter(" ", args.iter().map(|u| self.pp(u)));
                    });
                }
            }
            if ctx.alternate() {
                ctx.string(format!("/{}", t.idx())); // print unique ID
            }
        }
    }
}

/// An implementation of `ManagerCtx` using some notion of symbol and `HManager`
pub trait HManagerCtx
    : SymbolCtx
    + Manager<
        AST=AST,
        SymView=<Self as SymbolCtx>::View,
        SymBuilder=<Self as SymbolCtx>::Builder,
    >
{}

// auto impl
impl<U> HManagerCtx for U
where U: SymbolCtx,
      U: Manager<
        AST=AST,
        SymView=<Self as SymbolCtx>::View,
        SymBuilder=<Self as SymbolCtx>::Builder,
    >
{}

