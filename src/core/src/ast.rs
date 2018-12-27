
//! Abstraction over AST managers
//!
//! The core AST is parametrized by *symbols*, so that users can put
//! custom information in there.

use {
    std::{ hash, fmt, },
    crate::{ GC, },
    fxhash::{FxHashMap, FxHashSet, },
    batsmt_pretty as pp,
};

/// A temporary view of the definition of an AST node.
#[derive(Debug,Copy,Clone)]
pub enum View<'a, Sym, Sub> {
    Const(Sym), // symbol view
    App {
        f: Sub,
        args: &'a [Sub],
    }
}

/// A context with a notion of manager, AST, etc.
pub trait ManagerCtx {
    /// Annotation for constants (when viewed).
    type SymView : ?Sized;

    /// Annotation for constants (when creating them).
    type SymBuilder;

    /// The representation of an AST node.
    type AST : Clone + Eq + PartialEq + hash::Hash + fmt::Debug;

    /// The type of the manager itself.
    type M : Manager<AST=Self::AST, SymView=Self::SymView, SymBuilder=Self::SymBuilder>;
}

/// Public interface for an AST manager.
///
/// An AST manager is responsible for:
/// - allocating terms
/// - giving access to term's definitions
pub trait Manager : ManagerCtx<M=Self> + Sized {
    /// View the definition of the given AST.
    ///
    /// This should be as lightweight and fast as possible.
    fn view(&self, t: &Self::AST) -> View<&Self::SymView, Self::AST>;

    /// Create an application.
    fn mk_app(&mut self, f: Self::AST, args: &[Self::AST]) -> Self::AST;

    /// Create a constant from the given symbol.
    fn mk_const<U>(&mut self, s: U) -> Self::AST
        where U: std::borrow::Borrow<Self::SymView> + Into<Self::SymBuilder> ;

    /// Special AST node that should not be confused with anything else.
    fn sentinel(&mut self) -> Self::AST;

    /// Pretty-printable version of the given object
    fn pp<'a, T>(&'a self, x:T) -> ManagerAnd<Self, T>
        where Self : Sized, T : pp::Pretty1<Self> + 'a 
    { ManagerAnd(&self, x) }
}

/* FIXME: useless?
/// Something that contains an instance of a manager.
/// 
/// This is useful to embed a manager within something else, like a context
/// that would also have a literal mapping, a SAT solver, etc.
///
/// By implementing `with_manager`, a structure also implements `Manager`
/// with the same types for View, AST, etc.
pub trait HasManager {
    type M : Manager;
    fn m(&self) -> &Self::M;
    fn m_mut(&mut self) -> &mut Self::M;
}

mod manager {
    use {
        std::{ops::{Deref,DerefMut}},
        super::*,
    };

    impl<R:HasManager> ManagerCtx for R {
        type AST=<R::M as ManagerCtx>::AST;
        type SymView=<R::M as ManagerCtx>::SymView;
        type SymBuilder=<R::M as ManagerCtx>::SymBuilder;
        type M = R;
    }

    // auto impl by forwarding to the field `m`
    impl<R:HasManager> Manager for R {
        #[inline(always)]
        fn view(&self, t: &Self::AST) -> View<&Self::SymView, Self::AST>
        { self.m().view(t) }

        #[inline(always)]
        fn mk_app(&mut self, f: Self::AST, args: &[Self::AST]) -> Self::AST
        { self.m_mut().mk_app(f,args) }

        #[inline(always)]
        fn mk_const<U>(&mut self, s: U) -> Self::AST
            where U: std::borrow::Borrow<Self::SymView> + Into<Self::SymBuilder>
            { self.m_mut().mk_const(s) }

        #[inline(always)]
        fn sentinel(&mut self) -> Self::AST { self.m_mut().sentinel() }
    }

    // auto impl for ref
    impl<'a, M:Manager> HasManager for &'a mut M {
        type M = M;
        fn m(&self) -> &Self::M { self.deref() }
        fn m_mut(&mut self) -> &mut Self::M { self.deref_mut() }
    }
}
    */

/// A garbage collectible manager.
pub trait ManagerGC : Manager + GC<Element=<Self as ManagerCtx>::AST> {}

// Auto-impl
impl<M:Manager> ManagerGC for M where M: GC<Element=<M as ManagerCtx>::AST> {}

/// Used for printing, mainly.
pub struct ManagerAnd<'a, M:Manager, T>(pub &'a M, pub T);

/// Manager that knows how to pretty-print its AST
pub trait ManagerPP : Manager + Sized where Self::AST : pp::Pretty1<Self> {}

// Auto-impl
impl<M:Manager> ManagerPP for M where M::AST : pp::Pretty1<M> {}

mod manager_and {
    use super::*;

    impl<'a, M:Manager, T:pp::Pretty1<M>> pp::Pretty for ManagerAnd<'a,M,T> {
        fn pp(&self, ctx: &mut pp::Ctx) {
            let ManagerAnd(m,t) = self;
            t.pp_with(m, ctx)
        }
    }

    impl<'a, M:Manager, T:pp::Pretty1<M>> fmt::Display for ManagerAnd<'a,M,T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            pp::Pretty::pp_fmt(&self,out, false)
        }
    }
    impl<'a, M:Manager, T:pp::Pretty1<M>> fmt::Debug for ManagerAnd<'a,M,T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            pp::Pretty::pp_fmt(&self,out, true)
        }
    }
}

mod view {
    use super::*;

    impl<'a,Sym,Sub:Clone> View<'a, Sym, Sub> {
        /// Is this particular view an application?
        #[inline(always)]
        pub fn is_app(&self) -> bool { match self { View::App{..} => true, _ => false } }

        /// Is this particular view a constant?
        #[inline(always)]
        pub fn is_const(&self) -> bool { match self { View::Const(..) => true, _ => false } }

        /// Iterate over the immediate subterms of this view.
        pub fn subterms(&'a self) -> impl Iterator<Item=&'a Sub> + 'a {
            match &self {
                View::Const(_) => ViewIter::Nil,
                View::App{f, args} => ViewIter::App(f, args),
            }
        }
    }

    // state of the iterator
    enum ViewIter<'a,Sub:'a> {
        Nil,
        Args(&'a [Sub], usize),
        App(&'a Sub, &'a [Sub]),
    }

    /// Custom iterator over subterms.
    impl<'a, Sub> Iterator for ViewIter<'a, Sub> {
        type Item = &'a Sub;
        fn next(&mut self) -> Option<Self::Item> {
            match self {
                ViewIter::Nil => None,
                ViewIter::App(f,args) => {
                    let f = &**f; // separate pointer
                    *self = ViewIter::Args(args,0);
                    Some(f)
                },
                ViewIter::Args(args, n) => {
                    if *n == args.len() {
                        None
                    } else {
                        let t = &args[*n];
                        *n += 1;
                        Some(t)
                    }
                }
            }
        }
    }
}

/// Abstraction over sets of ASTs.
pub trait AstSet<AST:Clone> {
    /// Create a new set.
    fn new() -> Self where Self : Sized ;

    /// Clear all bits.
    fn clear(&mut self);

    fn len(&self) -> usize;

    /// Does the set contain this AST?
    fn contains(&self, ast: &AST) -> bool;

    /// Add the given term into the set.
    fn add(&mut self, ast: AST);

    /// Remove the term from the set.
    fn remove(&mut self, ast: &AST);

    // default functions.

    /// Add all the ASTs in the given slice.
    fn add_slice(&mut self, arr: &[AST]) {
        for ast in arr { self.add(ast.clone()) }
    }

    /// Add all the ASTs in the given iterator.
    fn add_iter<Q, I>(&mut self, iter:I)
        where I: Iterator<Item=Q>,
              Q: std::ops::Deref<Target=AST>
    {
        for ast in iter {
            self.add(ast.clone())
        }
    }
}

/// An AST Set that is "dense".
///
/// This indicates that it's based on some form of array or bitset, and
/// therefore that access should be very fast, possibly at the expense
/// of memory consumption.
pub trait AstDenseSet<AST:Clone> : AstSet<AST> {}

pub trait WithDenseSet<AST:Clone> : Manager {
    type DenseSet : AstDenseSet<AST>;
    fn new_dense_set() -> Self::DenseSet;
}

/// A manager that provides an implementation of a dense set.
pub trait ManagerWithDenseSet : Manager + WithDenseSet<<Self as ManagerCtx>::AST> {}

// auto-impl
impl<M> ManagerWithDenseSet for M
    where M : Manager, M : WithDenseSet<<M as ManagerCtx>::AST> {}

/// An AST Set that is "sparse".
///
/// This indicates that it's probably based on some form of hashtable, and
/// therefore that access is slower than `AstDenseSet`, but that it's more
/// memory efficient when storing only a few elements.
pub trait AstSparseSet<AST:Clone> : AstSet<AST> {}

pub trait WithSparseSet<AST:Clone> {
    type SparseSet : AstSparseSet<AST>;

    fn new_sparse_set() -> Self::SparseSet;
}

/// A manager that provides an implementation of a sparse set.
pub trait ManagerWithSparseSet
: Manager + WithSparseSet<<Self as ManagerCtx>::AST>
{
    /// Iterate over the given AST `t`, calling `f` on every subterm once.
    ///
    /// Allocates a `iter_dag::State` and uses it to iterate only once.
    /// For more sophisticated use (iterating on several terms, etc.)
    /// use `iter_dag::State` directly.
    fn iter_dag<F>(&self, t: &Self::AST, f: F)
        where Self : Sized,
              F: FnMut(&Self, &Self::AST)
    {
        let mut st = iter_dag::new(Self::new_sparse_set());
        st.iter(self, t, f)
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
    fn iter_suffix<Ctx,F1,F2>(
        &mut self, t: &Self::AST, ctx: &mut Ctx, fenter: F1, fexit: F2
    )
        where Self: Sized,
              F1: FnMut(&Self, &mut Ctx, &Self::AST) -> bool,
              F2: FnMut(&Self, &mut Ctx, &Self::AST)
    {
        let mut st = iter_suffix::State::new(Self::new_sparse_set());
        st.iter(self, t, ctx, fenter, fexit)
    }

    /// Compute size of the term, seen as a DAG.
    ///
    /// Each unique subterm is counted only once.
    fn size_dag(&self, t: &Self::AST) -> usize where Self : Sized {
        let mut n = 0;
        self.iter_dag(t, |_,_| { n += 1 });
        n
    }
}

// auto-impl
impl<M> ManagerWithSparseSet for M
    where M : Manager, M : WithSparseSet<<M as ManagerCtx>::AST> {}

/// Abstraction over maps whose keys are ASTs.
pub trait AstMap<AST, V> {
    /// Access the given key
    fn get(&self, ast: &AST) -> Option<&V>;

    /// Access the given key, return a mutable reference to its value
    fn get_mut(&mut self, ast: &AST) -> Option<&mut V>;

    /// Does the map contain this key?
    fn contains(&self, ast: &AST) -> bool;

    /// Insert a value
    fn insert(&mut self, ast: AST, v: V);

    /// Number of elements.
    fn len(&self) -> usize;

    /// Remove the given key
    fn remove(&mut self, ast: &AST);

    fn clear(&mut self);

    /// Is the map empty?
    #[inline(always)]
    fn is_empty(&self) -> bool { self.len() == 0 }
}

pub trait AstDenseMap<AST, V> : AstMap<AST, V> {
    /// Create a new map with `sentinel` as an element to fill the underlying storage.
    ///
    /// It is best if `sentinel` is efficient to clone.
    fn new(sentinel: V) -> Self;

    /// Access two disjoint locations, mutably.
    ///
    /// Precondition: the ASTs are distinct and in the map (panics otherwise).
    fn get2(&mut self, t1: AST, t2: AST) -> (&mut V, &mut V);
}

pub trait AstSparseMap<AST, V> : AstMap<AST, V> {
    /// Create a new empty sparse map.
    fn new() -> Self;
}

pub trait WithDenseMap<AST,V> {
    type DenseMap : AstDenseMap<AST, V>;

    fn new_dense_map(sentinel: V) -> Self::DenseMap;
}

/// A manager that provides an implementation of a dense map.
pub trait ManagerWithDenseMap<V: Clone>
    : Manager + WithDenseMap<<Self as ManagerCtx>::AST,V> {}

// auto-impl
impl<M, V:Clone> ManagerWithDenseMap<V> for M
    where M : Manager, M : WithDenseMap<<M as ManagerCtx>::AST,V> {}

pub trait WithSparseMap<AST, V:Clone> {
    type SparseMap : AstSparseMap<AST, V>;

    fn new_sparse_map() -> Self::SparseMap;
}

pub trait ManagerWithSparseMap<V: Clone>
    : Manager + WithSparseMap<<Self as ManagerCtx>::AST,V>
{
    /// Iterate over the given AST `t`, mapping every subterm using `f`.
    ///
    /// Allocates a `map_dag::State` and uses it to iterate.
    /// For more sophisticated use (mapping several terms, etc.)
    /// use `map_dag::State` directly.
    fn map<RSym, FSym, F>(&mut self, t: &Self::AST, fs: FSym, f: F) -> V
        where Self : Sized,
              for<'a> FSym: FnMut(&'a Self::SymView) -> RSym,
              for<'a> F: FnMut(&'a mut Self, &'a <Self as ManagerCtx>::AST, View<'a,RSym,V>) -> V
    {
        let mut st = map_dag::new(self, Self::new_sparse_map());
        st.map(&t, fs, f)
    }
}

// auto-impl
impl<M, V:Clone> ManagerWithSparseMap<V> for M
    where M : Manager, M : WithSparseMap<<M as ManagerCtx>::AST,V> {}

/// A hashset whose elements are AST nodes.
#[derive(Clone,Debug,Default)]
pub struct AstHashSet<M:Manager>(FxHashSet<M::AST>);

pub mod hash_set {
    use super::*;

    impl<M:Manager> AstSet<M::AST> for AstHashSet<M> {
        fn new() -> Self { AstHashSet(FxHashSet::default()) }

        #[inline(always)]
        fn contains(&self, t: &M::AST) -> bool { self.0.contains(t) }

        /// Insert a value
        #[inline(always)]
        fn add(&mut self, ast: M::AST) { self.0.insert(ast); }

        /// Number of elements.
        #[inline(always)]
        fn len(&self) -> usize { self.0.len() }

        /// Remove the given key
        #[inline(always)]
        fn remove(&mut self, ast: &M::AST) { self.0.remove(ast); }

        #[inline(always)]
        fn clear(&mut self) { self.0.clear() }
    }
}

/// Compute size of the term, seen as a tree.
pub fn ast_size_tree<M>(m: &mut M, t: &M::AST) -> usize
    where M:ManagerWithSparseMap<usize>
{
    m.map(
        t,
        |_| (),
        |_m, _u, view:View<(),usize>| {
            match view {
                View::Const(()) => 1usize,
                View::App{f, args} => {
                    args.iter().fold(1 + f, |x,y| x+y) // 1+sum of sizes
                },
            }
        })
}

/// A hashmap whose keys are AST nodes.
#[derive(Clone,Debug,Default)]
pub struct AstHashMap<M:Manager, V>(FxHashMap<M::AST,V>);

pub mod hash_map {
    use super::*;

    impl<M:Manager, V> AstMap<M::AST, V> for AstHashMap<M,V> {
        /// Access the given key
        #[inline(always)]
        fn get(&self, t: &M::AST) -> Option<&V> { self.0.get(t) }

        /// Access the given key, return a mutable reference to its value
        #[inline(always)]
        fn get_mut(&mut self, ast: &M::AST) -> Option<&mut V> {
            self.0.get_mut(ast)
        }

        /// Does the map contain this key?
        #[inline(always)]
        fn contains(&self, ast: &M::AST) -> bool { self.0.contains_key(ast) }

        /// Insert a value
        #[inline(always)]
        fn insert(&mut self, ast: M::AST, v: V) {
            self.0.insert(ast, v);
        }

        /// Number of elements.
        #[inline(always)]
        fn len(&self) -> usize { self.0.len() }

        /// Remove the given key
        #[inline(always)]
        fn remove(&mut self, ast: &M::AST) {
            self.0.remove(ast);
        }

        #[inline(always)]
        fn clear(&mut self) { self.0.clear() }
    }

    impl<M:Manager, V> AstSparseMap<M::AST, V> for AstHashMap<M,V> {
        fn new() -> Self { AstHashMap(FxHashMap::default()) }

    }
}

/// Iterate over sub-terms, with an immutable borrow.
///
/// Iteration over sub-terms, without repetition (sharing means a common
/// subterm will be traversed only once).
/// The order in which terms are traversed is not specified.
pub mod iter_dag {
    use super::*;

    #[derive(Clone)]
    pub struct State<M:Manager, Set> {
        st: Vec<M::AST>,
        seen: Set,
    }

    /// New state for iterating through subterms.
    ///
    /// - `m` is the AST manager
    /// - `seen` is a set of already processed subterms.
    pub fn new<M, S>(seen: S) -> State<M, S>
        where M:Manager, S: AstSet<M::AST>
    {
        State {seen, st: Vec::new(), }
    }

    impl<M, S> State<M, S> where M:Manager, S: AstSet<M::AST> {
        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `f` is the function to call once on every subterm, also given the manager
        pub fn iter<F>(&mut self, m: &M, t: &M::AST, mut f: F)
            where F: FnMut(&M, &M::AST)
        {
            if self.seen.len() > 0 && self.seen.contains(&t) { return }

            self.push(t.clone());
            while let Some(t) = self.st.pop() {
                if self.seen.contains(&t) {
                    continue
                } else {
                    self.seen.add(t.clone());
                    f(m, &t); // process `t`

                    match m.view(&t) {
                        View::Const(_) => (),
                        View::App{f,args} => {
                            self.st.push(f);
                            for a in args.iter() { self.st.push(a.clone()) }
                        },
                    }
                }
            }
        }

        /// local conditional push
        #[inline(always)]
        fn push(&mut self, t: M::AST) {
            if ! self.seen.contains(&t) {
                self.st.push(t)
            }
        }

        /// Clear state, forgetting all the subterms seen so far.
        pub fn clear(&mut self) {
            self.st.clear();
            self.seen.clear();
        }
    }

    impl<M:Manager,Set> fmt::Debug for State<M, Set> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "iter_dag.state")
        }
    }
}

/// Iterate over sub-terms, in suffix order, with an immutable manager ref.
///
/// Each sub-term is touched once, and parent terms are processed *after*
/// their subterms.
pub mod iter_suffix {
    use super::*;

    #[derive(Clone)]
    pub struct State<M:Manager, Set> {
        st: Vec<(EE,M::AST)>,
        seen: Set,
    }

    // flag: are we entering the term, or exiting it?
    #[repr(u8)]
    #[derive(Copy,Clone,PartialEq,Eq,Debug)]
    enum EE { Enter, Exit }

    impl<M:Manager, Set: AstSet<M::AST>> State<M, Set> {
        /// New state.
        pub fn new(seen: Set) -> Self {
            State {seen, st: Vec::new(), }
        }

        /// Iterate over the given AST `t`, calling a function on every subterm once.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `ctx` is a mutable context, shared among `fenter` and `fexit`
        /// - `fenter` is called _before_ processing a subterm.
        ///    If it returns `true`, the term is explored.
        /// - `fexit` is the function to call once on every subterm that `fenter` approved.
        pub fn iter<Ctx,F1,F2>(
            &mut self, m: &M,
            t: &M::AST, ctx: &mut Ctx,
            mut fenter: F1, mut fexit: F2
        )
            where F1: FnMut(&M, &mut Ctx, &M::AST)->bool,
                  F2: FnMut(&M, &mut Ctx, &M::AST)
        {
            if self.seen.len() > 0 && self.seen.contains(&t) { return }

            self.push_enter(t.clone());
            while let Some((ee,t)) = self.st.pop() {
                if ee == EE::Exit {
                    fexit(m, ctx, &t); // process `t`
                } else if self.seen.contains(&t) {
                    continue
                } else {
                    debug_assert_eq!(ee, EE::Enter);
                    self.seen.add(t.clone());

                    if !fenter(m, ctx, &t) {
                        continue // do not actually explore this
                    }

                    // exit `t` after processing subterms
                    self.push_exit(t.clone());

                    // explore subterms first
                    match m.view(&t) {
                        View::Const(_) => (),
                        View::App{f,args} => {
                            self.push_enter(f);
                            for a in args.iter() { self.push_enter(a.clone()) }
                        },
                    }
                }
            }
        }

        #[inline(always)]
        fn push_enter(&mut self, t: M::AST) { self.st.push((EE::Enter,t)); }

        #[inline(always)]
        fn push_exit(&mut self, t: M::AST) { self.st.push((EE::Exit,t)) }

        /// Clear state, forgetting all the subterms seen so far.
        pub fn clear(&mut self) {
            self.st.clear();
            self.seen.clear();
        }
    }

    impl<M:Manager, Set> fmt::Debug for State<M, Set> {
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

    pub struct State<'a, M:Manager, Map, R> {
        m: &'a mut M,
        st: State0<M, Map, R>,
    }

    // internal structure, separate from `m`
    #[derive(Clone)]
    struct State0<M: Manager, Map, R> {
        tasks: Vec<Task<M::AST>>,
        res: Vec<R>, // intermediate results
        cache: Map, // cached values
        args: Vec<R>, // temporary, for storing arguments when creating `View`
    }

    #[derive(Clone)]
    enum Task<AST> {
        // must be an application of `n` arguments.
        // Pops `n+1` from `res`, pushes one value onto `res`.
        Exit(AST),
        Enter(AST), // will eventually push one value onto `res`
    }

    /// New state using a hashmap.
    pub fn new_with_hashmap<'a,M,R>(m: &'a mut M) -> State<'a,M,AstHashMap<M,R>,R>
        where M: Manager, R: Clone
    {
        let map = AstHashMap::new();
        new(m, map)
    }

    /// New state using the given map.
    pub fn new<'a,M,Map,R>(m: &'a mut M, map: Map) -> State<'a,M,Map,R>
        where M: Manager, Map: AstMap<M::AST,R>, R: Clone
    {
        let st = State0 {
            cache: map, tasks: vec!(),
            res: vec!(), args: vec!(),
        };
        State {m, st, }
    }


    impl<'a,M,Map,R> State<'a,M,Map,R>
        where M: Manager, Map: AstMap<M::AST,R>, R: Clone
    {

        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// `f` is passed:
        /// - the manager itself
        /// - the original subterm
        /// - a view of the original subterm where its own immediate subterms
        ///   have been transformed by `f` already
        ///
        /// `fs` is used to transform symbol views into some owned value.
        /// You can return `()` if symbols are to be ignored.
        pub fn map<RSym, FSym, F>(&mut self, t: &M::AST, mut fs: FSym, mut f: F) -> R
            where for<'b> FSym: FnMut(&'b M::SymView) -> RSym,
                  for<'b> F: FnMut(&'b mut M, &'b M::AST, View<'b,RSym,R>) -> R
        {
            self.st.tasks.push(Task::Enter(t.clone()));
            while let Some(task) = self.st.tasks.pop() {
                match task {
                    Task::Enter(t) => {
                        match self.st.cache.get(&t) {
                            Some(u) => self.st.res.push(u.clone()), // cached
                            None => {
                                // explore subterms first, then schedule a call for `f`
                                let view_t = self.m.view(&t);
                                match view_t {
                                    View::Const(s) => {
                                        let s2 = fs(s);
                                        let view = View::Const(s2);
                                        drop(view_t);
                                        let r = f(self.m, &t, view);
                                        // put into cache and return immediately
                                        self.st.cache.insert(t, r.clone());
                                        self.st.res.push(r);
                                    }
                                    View::App{f, args} => {
                                        // process `f` and `args` before exiting `t`
                                        self.st.tasks.push(Task::Exit(t.clone()));
                                        self.st.tasks.push(Task::Enter(f));
                                        for u in args.iter() {
                                            self.st.tasks.push(Task::Enter(u.clone()));
                                        }
                                    }
                                }
                            },
                        }
                    },
                    Task::Exit(t) => {
                        let n = match self.m.view(&t) {
                            View::Const(_) => unreachable!(),
                            View::App{f:_, args} => args.len(),
                        };
                        // move arguments from stack to `st.args`
                        let head = self.st.res.pop().unwrap();
                        self.st.args.clear();
                        for _i in 0..n {
                            self.st.args.push(self.st.res.pop().unwrap());
                        }
                        let view = View::App{f: head, args: &self.st.args[..]};
                        let r = f(&mut self.m, &t, view);
                        self.st.cache.insert(t, r.clone()); // save in cache
                        self.st.res.push(r); // return result
                    },
                }
            }

            debug_assert_eq!(self.st.res.len(), 1);
            self.st.res.pop().unwrap()
        }
    }
}
