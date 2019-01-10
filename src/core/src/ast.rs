
//! Abstraction over AST managers
//!
//! The core AST is parametrized by *symbols*, so that users can put
//! custom information in there.

use {
    std::{ hash::Hash, fmt::{self, Debug}, },
    crate::{ gc, GC, },
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

/// Public interface for an AST manager, with associated types.
///
/// An AST manager is responsible for:
/// - allocating terms
/// - giving access to term's definitions
/// - pretty-printing terms
pub trait Manager : Sized {
    /// Annotation for constants (when viewed).
    type SymView : ?Sized + fmt::Display;

    /// Annotation for constants (when creating them).
    type SymBuilder;

    /// The representation of an AST node.
    type AST : Clone + Eq + PartialEq + Hash + Debug + HasID;

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
}

/// An object that may have a unique integer ID.
pub trait HasID {
    fn get_id(&self) -> Option<usize> { None }
}

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
        super::*,
    };

    // auto impl by forwarding to the field `m`
    impl<R:HasManager> Manager for R {
        type AST=<R::M as Manager>::AST;
        type SymView=<R::M as Manager>::SymView;
        type SymBuilder=<R::M as Manager>::SymBuilder;

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
        #[inline(always)]
        fn m(&self) -> &Self::M { &* self }
        #[inline(always)]
        fn m_mut(&mut self) -> &mut Self::M { &mut *self }
    }
}

/// A garbage collectible manager.
pub trait ManagerGC : Manager + GC<Element=<Self as Manager>::AST> {}

// Auto-impl
impl<M:Manager> ManagerGC for M where M: GC<Element=<M as Manager>::AST> {}

mod view {
    use super::*;

    impl<'a,Sym,Sub:Clone> View<'a, Sym, Sub> {
        /// Is this particular view an application?
        #[inline(always)]
        pub fn is_app(&self) -> bool { match self { View::App{..} => true, _ => false } }

        /// Is this particular view a constant?
        #[inline(always)]
        pub fn is_const(&self) -> bool { match self { View::Const(..) => true, _ => false } }

        /// Does this term have subterms?
        #[inline(always)]
        pub fn has_subterms(&self) -> bool {
            match self {
                View::Const(..) => false,
                View::App{..} => true,
            }
        }

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

/// AST-pretty printer, using `f` to print symbols.
pub fn pp_ast<M, F>(m: &M, t: &M::AST, f: &mut F, ctx: &mut pp::Ctx)
    where M: Manager,
          F: for<'a> FnMut(&'a M::SymView, &mut pp::Ctx)
{
    match m.view(t) {
        View::Const(s) => {
            f(&s, ctx);
        },
        View::App{f: ref f0, args} if args.len() == 0 => {
            pp_ast(m, f0, f, ctx); // just f
        },
        View::App{f: f0,args} => {
            ctx.sexp(|ctx| {
                pp_ast(m, &f0, f, ctx);
                for u in args.iter() {
                    ctx.space();
                    pp_ast(m, u, f, ctx);
                }
            });
        }
    }
    if ctx.alternate() {
        if let Some(i) = t.get_id() {
            ctx.string(format!("/{}", i)); // print unique ID
        }
    }
}

/// Create a temporary printing object from `m`.
pub fn pp<'a, M:Manager>(m: &'a M, t: &M::AST) -> impl 'a + fmt::Debug + fmt::Display + pp::Pretty {
    pp0::PP(m,t.clone())
}

mod pp0 {
    use super::*;
    pub(super) struct PP<'a, M:Manager>(pub &'a M, pub M::AST);

    impl<'a, M:Manager> pp::Pretty for PP<'a,M> {
        fn pp_into(&self, ctx: &mut pp::Ctx) {
            pp_ast(self.0, &self.1, &mut |s,ctx| { ctx.display(s); }, ctx)
        }
    }
    impl<'a, M:Manager> fmt::Debug for PP<'a, M> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result
        { pp::Pretty::pp_fmt(&self,out,true) }
    }
    impl<'a, M:Manager> fmt::Display for PP<'a, M> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result
        { pp::Pretty::pp_fmt(&self,out,false) }
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
pub trait DenseSet<AST:Clone> : AstSet<AST> {}

pub trait WithDenseSet<AST:Clone> : Manager {
    type DenseSet : DenseSet<AST>;
    fn new_dense_set() -> Self::DenseSet;
}

/// A manager that provides an implementation of a dense set.
pub trait ManagerWithDenseSet : Manager + WithDenseSet<<Self as Manager>::AST> {}

// auto-impl
impl<M> ManagerWithDenseSet for M
    where M : Manager, M : WithDenseSet<<M as Manager>::AST> {}

/// An AST Set that is "sparse".
///
/// This indicates that it's probably based on some form of hashtable, and
/// therefore that access is slower than `DenseSet`, but that it's more
/// memory efficient when storing only a few elements.
pub trait SparseSet<AST:Clone> : AstSet<AST> {}

pub trait WithSparseSet<AST:Clone> {
    type SparseSet : SparseSet<AST>;

    fn new_sparse_set() -> Self::SparseSet;
}

/// A manager that provides an implementation of a sparse set.
pub trait ManagerWithSparseSet
: Manager + WithSparseSet<<Self as Manager>::AST>
{}

// auto-impl
impl<M> ManagerWithSparseSet for M
    where M : Manager, M : WithSparseSet<<M as Manager>::AST> {}

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

pub trait DenseMap<AST, V> : AstMap<AST, V> {
    /// Create a new map with `sentinel` as an element to fill the underlying storage.
    ///
    /// It is best if `sentinel` is efficient to clone.
    fn new(sentinel: V) -> Self;

    /// Access the given key. It must be present.
    fn get_unchecked(&self, ast: &AST) -> &V;

    /// Access the given key, return a mutable reference to its value. It must be present.
    fn get_mut_unchecked(&mut self, ast: &AST) -> &mut V;

    /// Access two disjoint locations, mutably.
    ///
    /// Precondition: the ASTs are distinct and in the map (panics otherwise).
    fn get2(&mut self, t1: AST, t2: AST) -> (&mut V, &mut V);
}

pub trait SparseMap<AST, V> : AstMap<AST, V> {
    /// Create a new empty sparse map.
    fn new() -> Self;
}

pub trait WithDenseMap<AST,V> {
    type DenseMap : DenseMap<AST, V>;

    fn new_dense_map(sentinel: V) -> Self::DenseMap;
}

/// A manager that provides an implementation of a dense map.
pub trait ManagerWithDenseMap<V: Clone>
    : Manager + WithDenseMap<<Self as Manager>::AST,V> {}

// auto-impl
impl<M, V:Clone> ManagerWithDenseMap<V> for M
    where M : Manager, M : WithDenseMap<<M as Manager>::AST,V> {}

pub trait WithSparseMap<AST, V:Clone> {
    type SparseMap : SparseMap<AST, V>;

    fn new_sparse_map() -> Self::SparseMap;
}

pub trait ManagerWithSparseMap<V: Clone>
    : Manager + WithSparseMap<<Self as Manager>::AST,V>
{}

// auto-impl
impl<M, V:Clone> ManagerWithSparseMap<V> for M
    where M : Manager, M : WithSparseMap<<M as Manager>::AST,V> {}

/// A hashset whose elements are AST nodes.
#[derive(Clone,Debug,Default)]
pub struct HashSet<AST:Hash+Eq>(FxHashSet<AST>);

pub mod hash_set {
    use super::*;

    impl<AST:Hash+Eq> HashSet<AST> {
        /// New sparse set.
        pub fn new() -> Self { HashSet(FxHashSet::default()) }
    }

    impl<AST:Clone+Hash+Eq> AstSet<AST> for HashSet<AST> {
        fn new() -> Self { HashSet::new() }

        #[inline(always)]
        fn contains(&self, t: &AST) -> bool { self.0.contains(t) }

        /// Insert a value
        #[inline(always)]
        fn add(&mut self, ast: AST) { self.0.insert(ast); }

        /// Number of elements.
        #[inline(always)]
        fn len(&self) -> usize { self.0.len() }

        /// Remove the given key
        #[inline(always)]
        fn remove(&mut self, ast: &AST) { self.0.remove(ast); }

        #[inline(always)]
        fn clear(&mut self) { self.0.clear() }
    }

    impl<AST:Clone+Hash+Eq> SparseSet<AST> for HashSet<AST> {}

    impl<AST:Hash+Eq> gc::HasInternalMemory for HashSet<AST> {
        fn reclaim_unused_memory(&mut self) { self.0.shrink_to_fit() }
    }
}

/// A hashmap whose keys are AST nodes.
#[derive(Clone,Debug,Default)]
pub struct HashMap<AST:Eq+Hash, V>(FxHashMap<AST,V>);

pub mod hash_map {
    use super::*;

    impl<AST:Eq+Hash, V> AstMap<AST, V> for HashMap<AST,V> {
        /// Access the given key
        #[inline(always)]
        fn get(&self, t: &AST) -> Option<&V> { self.0.get(t) }

        /// Access the given key, return a mutable reference to its value
        #[inline(always)]
        fn get_mut(&mut self, ast: &AST) -> Option<&mut V> {
            self.0.get_mut(ast)
        }

        /// Does the map contain this key?
        #[inline(always)]
        fn contains(&self, ast: &AST) -> bool { self.0.contains_key(ast) }

        /// Insert a value
        #[inline(always)]
        fn insert(&mut self, ast: AST, v: V) {
            self.0.insert(ast, v);
        }

        /// Number of elements.
        #[inline(always)]
        fn len(&self) -> usize { self.0.len() }

        /// Remove the given key
        #[inline(always)]
        fn remove(&mut self, ast: &AST) {
            self.0.remove(ast);
        }

        #[inline(always)]
        fn clear(&mut self) { self.0.clear() }
    }

    impl<AST:Eq+Hash, V> SparseMap<AST, V> for HashMap<AST,V> {
        fn new() -> Self { HashMap(FxHashMap::default()) }
    }

    impl<AST:Eq+Hash, V> HashMap<AST,V> {
        /// New hashmap
        pub fn new() -> Self { HashMap(FxHashMap::default()) }
    }

    impl<AST:Hash+Eq,V> gc::HasInternalMemory for HashMap<AST,V> {
        fn reclaim_unused_memory(&mut self) { self.0.shrink_to_fit() }
    }
}

/// Iterate over sub-terms, with an immutable borrow.
///
/// Iteration over sub-terms, without repetition (sharing means a common
/// subterm will be traversed only once).
/// The order in which terms are traversed is not specified.
pub mod iter_dag {
    use super::*;

    /// State for iterating over subterms of term(s).
    #[derive(Clone)]
    pub struct State<AST, Set> {
        st: Vec<AST>,
        seen: Set,
    }

    /// New state for iterating through subterms.
    ///
    /// - `m` is the AST manager
    /// - `seen` is a set of already processed subterms.
    pub fn new<AST>() -> State<AST, HashSet<AST>>
        where AST: Clone+Eq+Hash
    {
        State {seen: HashSet::new(), st: Vec::new(), }
    }

    /// New state for iterating through subterms, using the given set.
    ///
    /// - `m` is the AST manager
    /// - `seen` is a set of already processed subterms.
    pub fn new_with<AST, S>(seen: S) -> State<AST, S>
        where AST: Clone, S: AstSet<AST>
    {
        State {seen, st: Vec::new(), }
    }

    impl<AST,S> State<AST,S>
        where AST:HasID+Debug+Eq+Hash+Clone, S: AstSet<AST>
    {
        /// local conditional push
        #[inline(always)]
        fn push(&mut self, t: AST) {
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

    macro_rules! iter_impl {
        ($self:ident, $m:ident, $t:ident, $f:ident) => {
            if $self.seen.len() > 0 && $self.seen.contains(& $t) { return }

            $self.push($t.clone());
            while let Some(t) = $self.st.pop() {
                if $self.seen.contains(&t) {
                    continue
                } else {
                    $self.seen.add(t.clone());
                    $f($m, &t); // process `t`

                    match $m.view(&t) {
                        View::Const(_) => (),
                        View::App{f,args} => {
                            $self.st.push(f);
                            for a in args.iter() {
                                $self.st.push(a.clone())
                            }
                        },
                    }
                }
            }
        }
    }

    impl<AST, S> State<AST, S> where AST:HasID+Debug+Eq+Hash+Clone, S: AstSet<AST> {
        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `f` is the function to call once on every subterm, also given the manager
        pub fn iter<M, F>(&mut self, m: &M, t: &M::AST, mut f: F)
            where F: FnMut(&M, &M::AST),
                  M: Manager<AST=AST>
        {
            iter_impl!(self, m, t, f);
        }

        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// This version threads a mutable context `&mut M`.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `f` is the function to call once on every subterm, also given the manager
        pub fn iter_mut<M, F>(&mut self, m: &mut M, t: &M::AST, mut f: F)
            where F: FnMut(&mut M, &M::AST),
                  M: Manager<AST=AST>
        {
            iter_impl!(self, m, t, f);
        }
    }

    impl<AST, S> gc::HasInternalMemory for State<AST, S>
        where AST:Clone, S: AstSet<AST> + gc::HasInternalMemory {
        fn reclaim_unused_memory(&mut self) {
            self.st.shrink_to_fit();
            self.seen.reclaim_unused_memory();
        }
    }

    impl<AST,Set> Debug for State<AST, Set> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "iter_dag.state")
        }
    }
}

/// Iterate over the given AST `t`, calling `f` on every subterm once.
///
/// Allocates a `iter_dag::State` and uses it to iterate only once.
/// For more sophisticated use (iterating on several terms, etc.)
/// use `iter_dag::State` directly.
pub fn iter_dag<M, F>(m: &M, t: &M::AST, f: F)
    where M: Manager, F: FnMut(&M, &M::AST)
{
    let mut st = iter_dag::new();
    st.iter(m, t, f)
}

/// Compute size of the term, seen as a DAG.
///
/// Each unique subterm is counted only once.
pub fn size_dag<M>(m: &M, t: &M::AST) -> usize where M : Manager {
    let mut n = 0;
    iter_dag(m, t, |_,_| { n += 1 });
    n
}

/// Iterate over sub-terms, in suffix order, with an immutable manager ref.
///
/// Each sub-term is touched once, and parent terms are processed *after*
/// their subterms.
pub mod iter_suffix {
    use super::*;

    #[derive(Clone)]
    pub struct State<AST, Set> {
        st: Vec<(EE,AST)>,
        seen: Set,
    }

    // flag: are we entering the term, or exiting it?
    #[repr(u8)]
    #[derive(Copy,Clone,PartialEq,Eq,Debug)]
    enum EE { Enter, Exit }

    impl<AST:Eq+Hash+Clone> State<AST, HashSet<AST>> {
        /// New state, using `HashSet`.
        pub fn new() -> Self {
            State {seen: HashSet::new(), st: Vec::new(), }
        }
    }

    impl<AST:Clone, Set: AstSet<AST>> State<AST, Set> {
        /// New state, using given set.
        pub fn new_with(seen: Set) -> Self {
            State {seen, st: Vec::new(), }
        }
    }

    impl<AST,Set> State<AST, Set> where AST:HasID+Debug+Eq+Hash+Clone, Set: AstSet<AST> {
        /// Iterate over the given AST `t`, calling a function on every subterm once.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `ctx` is a mutable context, shared among `fenter` and `fexit`
        /// - `fenter` is called _before_ processing a subterm.
        ///    If it returns `true`, the term is explored.
        /// - `fexit` is the function to call once on every subterm that `fenter` approved.
        pub fn iter<M,Ctx,F1,F2>(
            &mut self, m: &M,
            t: &M::AST, ctx: &mut Ctx,
            mut fenter: F1, mut fexit: F2
        )
            where F1: FnMut(&M, &mut Ctx, &M::AST)->bool,
                  F2: FnMut(&M, &mut Ctx, &M::AST),
                  M: Manager<AST=AST>
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
        fn push_enter(&mut self, t: AST) { self.st.push((EE::Enter,t)); }

        #[inline(always)]
        fn push_exit(&mut self, t: AST) { self.st.push((EE::Exit,t)) }

        /// Clear state, forgetting all the subterms seen so far.
        pub fn clear(&mut self) {
            self.st.clear();
            self.seen.clear();
        }
    }

    impl<AST, Set> fmt::Debug for State<AST, Set> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "iter_suffix.state")
        }
    }

    impl<AST, S> gc::HasInternalMemory for State<AST, S>
        where AST:Clone, S: AstSet<AST> + gc::HasInternalMemory {
        fn reclaim_unused_memory(&mut self) {
            self.st.shrink_to_fit();
            self.seen.reclaim_unused_memory();
        }
    }
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
pub fn iter_suffix<M,Ctx,F1,F2>(
    m: &mut M, t: &M::AST, ctx: &mut Ctx, fenter: F1, fexit: F2
)
    where M: Manager,
          F1: FnMut(&M, &mut Ctx, &M::AST) -> bool,
          F2: FnMut(&M, &mut Ctx, &M::AST)
{
    let mut st = iter_suffix::State::new();
    st.iter(m, t, ctx, fenter, fexit)
}

/// Map sub-terms to arbitrary values.
///
/// Iteration over sub-terms, without repetition (sharing means a common
/// subterm will be traversed only once).
pub mod map_dag {
    use super::*;

    /// State for mapping.
    ///
    /// This state is useful to re-use internal structures between calls,
    /// possibly using `clear` to clean caches.
    /// If `clear` is not used, it accelerates mapping by providing memoization/caching.
    #[derive(Clone)]
    pub struct State<AST, Map, R> {
        tasks: Vec<Task<AST>>,
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
    pub fn new<AST,R>() -> State<AST,HashMap<AST,R>,R>
        where AST:Eq+Hash, R: Clone
    {
        let map = HashMap::new();
        new_with(map)
    }

    /// New state using the given map.
    pub fn new_with<'a,AST,Map,R>(map: Map) -> State<AST,Map,R>
        where Map: AstMap<AST,R>, R: Clone
    {
        State {
            cache: map, tasks: vec!(),
            res: vec!(), args: vec!(),
        }
    }


    impl<AST,Map,R> State<AST,Map,R>
        where AST:HasID+Debug+Clone+Eq+Hash, Map: AstMap<AST,R>, R: Clone
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
        pub fn map<M, RSym, FSym, F>(
            &mut self,
            m: &mut M,
            t: &M::AST, mut fs: FSym, mut f: F
        ) -> R
            where M: Manager<AST=AST>,
                  for<'b> FSym: FnMut(&'b M::SymView) -> RSym,
                  for<'b> F: FnMut(&'b mut M, &'b M::AST, View<'b,RSym,R>) -> R
        {
            self.tasks.push(Task::Enter(t.clone()));
            while let Some(task) = self.tasks.pop() {
                match task {
                    Task::Enter(t) => {
                        match self.cache.get(&t) {
                            Some(u) => self.res.push(u.clone()), // cached
                            None => {
                                // explore subterms first, then schedule a call for `f`
                                let view_t = m.view(&t);
                                match view_t {
                                    View::Const(s) => {
                                        let s2 = fs(s);
                                        let view = View::Const(s2);
                                        drop(view_t);
                                        let r = f(m, &t, view);
                                        // put into cache and return immediately
                                        self.cache.insert(t, r.clone());
                                        self.res.push(r);
                                    }
                                    View::App{f, args} => {
                                        // process `f` and `args` before exiting `t`
                                        self.tasks.push(Task::Exit(t.clone()));
                                        self.tasks.push(Task::Enter(f));
                                        for u in args.iter() {
                                            self.tasks.push(Task::Enter(u.clone()));
                                        }
                                    }
                                }
                            },
                        }
                    },
                    Task::Exit(t) => {
                        let n = match m.view(&t) {
                            View::Const(_) => unreachable!(),
                            View::App{f:_, args} => args.len(),
                        };
                        // move arguments from stack to `st.args`
                        let head = self.res.pop().unwrap();
                        self.args.clear();
                        for _i in 0..n {
                            self.args.push(self.res.pop().unwrap());
                        }
                        let view = View::App{f: head, args: &self.args[..]};
                        let r = f(m, &t, view);
                        self.cache.insert(t, r.clone()); // save in cache
                        self.res.push(r); // return result
                    },
                }
            }

            debug_assert_eq!(self.res.len(), 1);
            self.res.pop().unwrap()
        }
    }


    impl<AST,Map,R> gc::HasInternalMemory for State<AST,Map,R>
        where AST:Clone, R: Clone, Map: AstMap<AST,R> + gc::HasInternalMemory {
        fn reclaim_unused_memory(&mut self) {
            self.cache.reclaim_unused_memory();
            self.tasks.shrink_to_fit();
            self.args.shrink_to_fit();
            self.res.shrink_to_fit();
        }
    }
}

/// Iterate over the given AST `t`, mapping every subterm using `f`.
///
/// Allocates a `map_dag::State` and uses it to iterate.
/// For more sophisticated use (mapping several terms, etc.)
/// use `map_dag::State` directly.
pub fn map_dag<M, RSym, FSym, F, R>(m: &mut M, t: &M::AST, fs: FSym, f: F) -> R
    where M : Manager,
          R: Clone,
          for<'a> FSym: FnMut(&'a M::SymView) -> RSym,
          for<'a> F: FnMut(&'a mut M, &'a <M as Manager>::AST, View<'a,RSym,R>) -> R
{
    let mut st = map_dag::new();
    st.map(m, &t, fs, f)
}
