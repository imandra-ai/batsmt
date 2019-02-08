
//! AST manager with hashconsing.
//!
//! The AST manager stores AST nodes, referred to via `AST`. These nodes can
//! be used to represent sorts, terms, formulas, theory terms, etc.

extern crate batsmt_core;

pub mod symbol;

use {
    std::{
        slice, u32, marker::PhantomData, fmt,
    },
    batsmt_core::{ ast::{self,Manager}, ast_u32, gc, AstView, },
    fxhash::{FxHashMap},
    bit_set::BitSet,
    batsmt_pretty as pp,
};

pub use {
    crate::symbol::{
        SymbolCtx, SymbolManager,
        str::StrManager as StrSymbolManager,
        //str_id::ScopedManager,
    },
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
    args: ArrOrVec<AST>,
    phantom: PhantomData<&'a ()>,
}

// Number of arguments for a "small" term application
const N_SMALL_APP : usize = 3;

/// A custom small-vec with a raw pointer. This is used to store the arguments
/// of an `app` term.
#[derive(Copy,Clone)]
pub(crate) union ArrOrVec<T : Copy> {
    arr: [T; N_SMALL_APP],
    ptr: * const T, // will be shared between vec and hashmap
}

fn check_len_u16(len: usize) {
    use std::u16;
    if len > u16::MAX as usize {
        panic!("cannot make an AST application of length {}", len);
    }
}

impl AppStored<'static> {
    pub fn new(f: AST, args: &[AST]) -> Self {
        let len = args.len();
        check_len_u16(len);

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
            phantom: PhantomData,
        };
        debug_assert_eq!(r.args(), args, "expected {:?} got {:?}", args, r.args());
        r
    }

    pub(crate) const SENTINEL : Self =
        AppStored {
            f: AST::SENTINEL, len: 0, phantom: PhantomData,
            args: ArrOrVec{ arr: [AST::SENTINEL; N_SMALL_APP] }
        };

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
    fn f(&self) -> AST { self.f }

    #[inline]
    fn view<S:SymbolCtx>(&self) -> HView<S> {
        AstView::App {f: &self.f, args: self.args()}
    }

    #[inline(always)]
    fn args<'b: 'a>(&'b self) -> &'b [AST] {
        let len = self.len as usize;
        if len <= N_SMALL_APP {
            unsafe { &self.args.arr[..len] }
        } else {
            unsafe {slice::from_raw_parts(self.args.ptr, len)}
        }
    }

    // Temporary-lived key, borrowing the given slice
    fn mk_ref(f: AST, args: &[AST]) -> Self {
        let len = args.len();
        check_len_u16(len);
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
            phantom: PhantomData,
        };
        debug_assert_eq!(r.args(), args, "expected {:?} got {:?}", args, r.args());
        r
    }

    fn to_owned(self) -> AppStored<'static> {
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
    #[inline]
    fn hash<H:Hasher>(&self, h: &mut H) {
        self.f.hash(h);
        self.args().hash(h)
    }
}

impl<'a> fmt::Debug for AppStored<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "({:?} {:?})", self.f, self.args())
    }
}

/*
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
*/

#[inline(always)]
pub fn ast_is_app(t: AST) -> bool { t.idx() & 0b1 == 0 }

#[inline(always)]
pub fn mk_ast_app(i: u32) -> AST { ast_u32::manager_util::ast_from_u32(i << 1) }

#[inline(always)]
pub fn ast_is_const(t: AST) -> bool { t.idx() & 0b1 == 1 }

#[inline(always)]
pub fn mk_ast_const(i: u32) -> AST { ast_u32::manager_util::ast_from_u32((i << 1) | 0b1) }

/// Index in the corresponding vector.
#[inline(always)]
pub const fn ast_idx(t: AST) -> u32 { (t.idx() >> 1) }

/// Maximum index that can fit in `AST`
const AST_MAX_IDX : u32 = (u32::MAX >> 1);

/*
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
*/

/// A vector with some additional metadata.
struct ManagedVec<T> {
    sentinel: T,
    vec: Vec<T>,
    gc_alive: BitSet,
    recycle: Vec<u32>, // slots in `nodes` that are available
}

impl<T> std::ops::Deref for ManagedVec<T> {
    type Target = Vec<T>;
    #[inline]
    fn deref(&self) -> &Self::Target { &self.vec }
}

impl<T> std::ops::DerefMut for ManagedVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.vec }
}

impl<T: Clone> ManagedVec<T> {
    /// New managed vec.
    fn new(sentinel: T) -> Self {
        ManagedVec {
            sentinel,
            vec: vec!(), gc_alive: BitSet::new(),
            recycle: vec!(), }
    }

    /// allocate a new AST ID, and return the slot it should live in
    fn allocate_id(&mut self) -> (u32, &mut T) {
        match self.recycle.pop() {
            Some(n) => {
                let slot = &mut self.vec[n as usize];
                (n,slot)
            },
            None => {
                let n = self.vec.len();
                // does `n` fit in an AST?
                if n > AST_MAX_IDX as usize {
                    panic!("cannot allocate more AST nodes")
                }
                self.vec.push(self.sentinel.clone());
                let slot = &mut self.vec[n];
                (n as u32, slot)
            }
        }
    }

    #[inline]
    fn alive(&self, i: u32) -> bool {
        self.gc_alive.contains(i as usize)
    }

    #[inline]
    fn mark_alive(&mut self, i: u32) -> bool {
        self.gc_alive.insert(i as usize)
    }

    #[inline]
    fn unmark_all(&mut self) {
        self.gc_alive.clear()
    }

    /// Number of terms
    fn len(&self) -> usize {
        let a = self.vec.len();
        let b = self.recycle.len();
        debug_assert!(a >= b);
        a - b
    }

    fn reclaim_unused_memory(&mut self) {
        self.vec.shrink_to_fit();
        self.gc_alive.shrink_to_fit();
        self.recycle.shrink_to_fit();
    }

    /// Recycle element at index `i`, using `f` to free its content if needed.
    fn recycle<F>(&mut self, i: u32, f: F)
        where F: FnOnce(T)
    {
        // remove node from `self.vec[i]` and move it locally
        let mut value = self.sentinel.clone();
        std::mem::swap(&mut self.vec[i as usize], &mut value);
        self.recycle.push(i);
        f(value); // free `value` using `f`
    }


    /// Collect non-roots, return number of collected values.
    fn gc_retain_roots<F>(&mut self, mut f: F) -> usize 
        where F: FnMut(T)
    {
        let len = self.vec.len();
        let mut count = 0;
        for i in 0 .. len {
            if ! self.gc_alive.contains(i as usize) {
                // collect
                count += 1;
                // remove node from `self.nodes[i]` and move it locally
                self.recycle(i as u32, |x| f(x))
            }
        }
        count
    }
}

/// The AST manager, responsible for storing and creating AST nodes
pub struct HManager<S:SymbolManager> {
    apps: ManagedVec<AppStored<'static>>,
    consts: ManagedVec<S::Ref>,
    tbl_app: FxHashMap<AppStored<'static>, AST>, // hashconsing of applications
    sym_m: S,
    gc_stack: Vec<AST>, // temporary vector for GC marking
}

impl<S:SymbolManager> Manager for HManager<S> {
    type SymBuilder = S::Builder;
    type SymView = S::View;
    type AST = AST;

    #[inline(always)]
    fn view<'a>(&'a self, &t: &AST) -> HView<'a, S> {
        if ast_is_app(t) {
            self.apps[ast_idx(t) as usize].view::<S>()
        } else {
            let view = self.sym_m.view(self.consts[ast_idx(t) as usize]);
            AstView::Const(view)
        }
    }

    #[inline(always)]
    fn is_app(&self, &t: &AST) -> bool { ast_is_app(t) }

    #[inline(always)]
    fn is_const(&self, &t: &AST) -> bool { ast_is_const(t) }

    /// `m.mk_app(f, args)` creates the application of `f` to `args`.
    ///
    /// If the term is structurally equal to an existing term, then this
    /// ensures the exact same AST is returned ("hashconsing").
    /// If `args` is empty, return `f`.
    fn mk_app(&mut self, f: AST, args: &[AST]) -> AST {
        if args.len() == 0 { return f }

        let k = AppStored::mk_ref(f, args);

        // borrow multiple fields
        let HManager {apps, tbl_app, ..} = self;

        match tbl_app.get(&k) {
            Some(&a) => a, // fast path
            None => {
                // insert
                let (n, slot) = apps.allocate_id();
                let ast = mk_ast_app(n);
                // make 2 owned copies of the key
                let k = k.to_owned();
                *slot = k.clone();
                tbl_app.insert(k, ast);
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
    fn mk_const<U>(&mut self, s: U) -> AST
        where U: std::borrow::Borrow<Self::SymView> + Into<Self::SymBuilder>
    {
        let r = self.sym_m.build(s);
        let (n, slot) = self.consts.allocate_id();
        *slot = r;
        mk_ast_const(n)
    }

    fn sentinel(&mut self) -> AST { AST::SENTINEL }
}

impl<S:SymbolManager> HManager<S> {
    /// Create a new AST manager
    pub fn new() -> Self {
        let mut tbl_app = FxHashMap::default();
        tbl_app.reserve(1_024);
        let sym_m = S::new();
        HManager {
            apps: ManagedVec::new(AppStored::SENTINEL),
            consts: ManagedVec::new(sym_m.sentinel()),
            tbl_app,
            sym_m,
            gc_stack: Vec::new(),
        }
    }

    /// Number of terms
    pub fn n_terms(&self) -> usize {
        self.apps.len() + self.consts.len()
    }

    fn gc_alive(&self, t: AST) -> bool {
        if ast_is_app(t) {
            self.apps.alive(ast_idx(t))
        } else {
            self.consts.alive(ast_idx(t))
        }
    }

    fn gc_mark_alive(&mut self, t: AST) -> bool {
        if ast_is_app(t) {
            self.apps.mark_alive(ast_idx(t))
        } else {
            self.consts.mark_alive(ast_idx(t))
        }
    }

    fn gc_unmark_all(&mut self) {
        self.apps.unmark_all();
        self.consts.unmark_all();
    }

    // traverse and mark all elements on `stack` and their subterms
    fn gc_traverse_and_mark(&mut self) {
        while let Some(ast) = self.gc_stack.pop() {
            if self.gc_alive(ast) {
                continue; // subgraph already marked and traversed
            }
            self.gc_mark_alive(ast);

            if ast_is_app(ast) {
                let app = &self.apps[ast_idx(ast) as usize];
                // explore subterms, too
                self.gc_stack.push(app.f);
                for &a in app.args() { self.gc_stack.push(a) };
            }
        }
    }

    // collect dead values, return number of collected values
    fn gc_retain_roots(&mut self) -> usize {
        let mut count = 0;

        let HManager{apps, tbl_app, consts, sym_m, ..} = self;

        count += apps.gc_retain_roots(|mut app| { 
            // remove from table
            tbl_app.remove_entry(&app);
            unsafe { app.free() }
        });

        count += consts.gc_retain_roots(|s| {
            sym_m.free(s)
        });
        count
    }

    fn gc_mark_root(&mut self, &ast: &AST) {
        // mark subterms transitively, using recursion stack
        if ! self.gc_alive(ast) {
            self.gc_stack.push(ast);
            self.gc_traverse_and_mark();
        }
    }

    fn gc_collect(&mut self) -> usize {
        let n = self.gc_retain_roots();
        self.gc_unmark_all();
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
        self.apps.reclaim_unused_memory();
        self.consts.reclaim_unused_memory();
        self.tbl_app.shrink_to_fit();
        self.gc_stack.shrink_to_fit();
    }
}


/// GC for a manager's internal nodes
impl<S> gc::GC for HManager<S> where S: SymbolManager {
    type Element = AST;
    fn mark_root(&mut self, ast: &AST) { self.gc_mark_root(ast) }
    fn collect(&mut self) -> usize { self.gc_collect() }
}

/// An AST can be printed, given a manager, if the symbols are pretty
impl<S:SymbolManager> pp::Pretty1<AST> for HManager<S> {
    fn pp1_into(&self, t: &AST, ctx: &mut pp::Ctx) {
        ast::pp_ast(self, t, &mut |s, ctx| { self.sym_m.pp1_into(&s, ctx) }, ctx)
    }
}
