
//! Abstraction over AST managers
//!
//! The core AST is parametrized by *symbols*, so that users can put
//! custom information in there.

use {
    std::{ hash, fmt, },
    crate::{ GC, },
    fxhash::FxHashMap,
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

/// Public interface for an AST manager.
///
/// An AST manager is responsible for:
/// - allocating terms
/// - giving access to term's definitions
pub trait Manager {
    /// Annotation for constants.
    type Sym;

    /// The representation of an AST node.
    type AST : Clone + Eq + PartialEq + hash::Hash + fmt::Debug;

    /// View the definition of the given AST.
    ///
    /// This should be as lightweight and fast as possible.
    fn view<'a>(&'a self, t: &'a Self::AST) -> View<'a, &'a Self::Sym, Self::AST>;

    /// Create an application.
    fn mk_app(&mut self, f: Self::AST, args: &[Self::AST]) -> Self::AST;

    /// Create a constant from the given symbol.
    fn mk_const(&mut self, s: Self::Sym) -> Self::AST;

    /// Pretty-printable version of the given object
    fn pp<'a, T:PrettyM<M=Self>+'a>(&'a self, x:T)
        -> ManagerAnd<Self, T> where Self : Sized { ManagerAnd(&self, x) }
}

/// A garbage collectible manager.
pub trait ManagerGC : Manager + GC<Element=<Self as Manager>::AST> {}

// Auto-impl
impl<M:Manager> ManagerGC for M where M: GC<Element=<M as Manager>::AST> {}

/// Used for printing, mainly.
pub struct ManagerAnd<'a, M:Manager, T>(pub &'a M, pub T);

/// Manager that knows how to pretty-print its AST
pub trait ManagerPP : Manager + Sized where Self::AST : PrettyM<M=Self> {}

// Auto-impl
impl<M:Manager> ManagerPP for M where M::AST : PrettyM<M=M> {}

mod manager_and {
    use super::*;

    impl<'a, T:PrettyM> pp::Pretty for ManagerAnd<'a,T::M,T> {
        fn pp(&self, ctx: &mut pp::Ctx) {
            let ManagerAnd(m,t) = self;
            t.pp_m(m, ctx)
        }
    }

    impl<'a, T:PrettyM> fmt::Display for ManagerAnd<'a,T::M,T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            pp::Pretty::pp_fmt(&self,out, false)
        }
    }
    impl<'a, T:PrettyM> fmt::Debug for ManagerAnd<'a,T::M,T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            pp::Pretty::pp_fmt(&self,out, true)
        }
    }
}

/// Objects that can be pretty-printed if paired with a manager
pub trait PrettyM {
    type M : Manager;
    fn pp_m(&self, m: &Self::M, ctx: &mut pp::Ctx);
}

pub mod pretty_m {
    use super::*;

    impl<'a, T:PrettyM> PrettyM for &'a T {
        type M = T::M;
        fn pp_m(&self, m: &Self::M, ctx: &mut pp::Ctx) { (*self).pp_m(m,ctx) }
    }

    // render array in a S-expr
    impl<'a, T:PrettyM> PrettyM for &'a [T] {
        type M = T::M;
        fn pp_m(&self, m: &Self::M, ctx: &mut pp::Ctx) {
            let v: Vec<_> = self.iter().map(|x| m.pp(x)).collect();
            ctx.sexp(|ctx| { ctx.array(pp::space(), &v); });
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

/// A manager that provides an implementation of a dense set.
pub trait ManagerWithDenseSet : Manager {
    type DenseSet : AstDenseSet<Self::AST>;

    fn new_dense_set() -> Self::DenseSet;
}

/// An AST Set that is "sparse".
///
/// This indicates that it's probably based on some form of hashtable, and
/// therefore that access is slower than `AstDenseSet`, but that it's more
/// memory efficient when storing only a few elements.
pub trait AstSparseSet<AST:Clone> : AstSet<AST> {}

/// A manager that provides an implementation of a sparse set.
pub trait ManagerWithSparseSet : Manager {
    type SparseSet : AstSparseSet<Self::AST>;

    fn new_sparse_set() -> Self::SparseSet;
}

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

/// A manager that provides an implementation of a dense map.
pub trait ManagerWithDenseMap<V: Clone> : Manager {
    type DenseMap : AstDenseMap<Self::AST, V>;

    fn new_dense_map() -> Self::DenseMap;
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

/// Iterate over sub-terms.
///
/// Iteration over sub-terms, without repetition (sharing means a common
/// subterm will be traversed only once).
/// The order in which terms are traversed is not specified.
pub mod iter_dag {
    use super::*;

    pub struct State<'a, M:ManagerWithSparseSet> {
        m: &'a mut M,
        st: State0<M>,
    }

    // internal structure, separate from `m`
    #[derive(Clone)]
    struct State0<M:ManagerWithSparseSet> {
        st: Vec<M::AST>,
        seen: M::SparseSet,
    }

    impl<'a, M> State<'a, M> where M:ManagerWithSparseSet {
        /// New state
        pub fn new(m: &'a mut M) -> Self {
            State { m, st: State0::new(M::new_sparse_set()), }
        }

        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// ## Params
        /// - `self` is the set of already seen terms, and will be mutated.
        /// - `t` is the term to recursively explore
        /// - `f` is the function to call once on every subterm, also given the manager
        pub fn iter<F>(&mut self, t: M::AST, mut f: F)
            where F: FnMut(&mut M, M::AST)
        {
            if self.st.seen.len() > 0 && self.st.seen.contains(&t) { return }

            self.st.push(t);
            while let Some(t) = self.st.st.pop() {
                if self.st.seen.contains(&t) {
                    continue
                } else {
                    self.st.seen.add(t.clone());
                    f(&mut self.m, t.clone()); // process `t`

                    match self.m.view(&t) {
                        View::Const(_) => (),
                        View::App{f,args} => {
                            self.st.push(f);
                            for a in args.iter() { self.st.push(a.clone()) }
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

    impl<M:ManagerWithSparseSet> State0<M> {
        fn new(s: M::SparseSet) -> Self {
            Self {seen: s, st: Vec::new(), }
        }

        /// local conditional push
        fn push(&mut self, t: M::AST) {
            if ! self.seen.contains(&t) {
                self.st.push(t)
            }
        }
    }

    impl<'a, M:ManagerWithSparseSet> fmt::Debug for State<'a, M> {
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

    pub struct State<'a, M:ManagerWithSparseSet> {
        m: &'a mut M,
        st: State0<M>,
    }

    // flag: are we entering the term, or exiting it?
    #[repr(u8)]
    #[derive(Copy,Clone,PartialEq,Eq,Debug)]
    enum EE { Enter, Exit }

    // internal structure, separate from `m`
    #[derive(Clone)]
    struct State0<M:ManagerWithSparseSet> {
        st: Vec<(EE,M::AST)>,
        seen: M::SparseSet,
    }

    impl<'a, M:ManagerWithSparseSet> State<'a, M> {
        /// New state.
        pub fn new(m: &'a mut M) -> Self {
            State { m, st: State0::new(M::new_sparse_set()), }
        }

        /// New state, using the given `seen` set.
        pub fn new_with_seen(m: &'a mut M, seen: M::SparseSet) -> Self {
            State { m, st: State0::new(seen), }
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
            &mut self, t: M::AST, ctx: &mut Ctx, mut fenter: F1, mut fexit: F2
        )
            where F1: FnMut(&mut Ctx, M::AST)->bool, F2: FnMut(&mut Ctx, M::AST)
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
                    self.st.seen.add(t.clone());

                    if !fenter(ctx, t.clone()) {
                        continue // do not actually explore this
                    }

                    // exit `t` after processing subterms
                    self.st.push_exit(t.clone());

                    // explore subterms first
                    match self.m.view(&t) {
                        View::Const(_) => (),
                        View::App{f,args} => {
                            self.st.push_enter(f);
                            for a in args.iter() { self.st.push_enter(a.clone()) }
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

    impl<M:ManagerWithSparseSet> State0<M> {
        fn new(seen: M::SparseSet) -> Self {
            Self {seen, st: Vec::new(), }
        }

        #[inline(always)]
        fn push_enter(&mut self, t: M::AST) { self.st.push((EE::Enter,t)); }

        #[inline(always)]
        fn push_exit(&mut self, t: M::AST) { self.st.push((EE::Exit,t)) }
    }

    impl<'a, M:ManagerWithSparseSet> fmt::Debug for State<'a, M> {
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

    pub struct State<'a, M:Manager, R> {
        m: &'a mut M,
        st: State0<M, R>,
    }

    // internal structure, separate from `m`
    #[derive(Clone)]
    struct State0<M: Manager, R> {
        tasks: Vec<Task<M::AST>>,
        res: Vec<R>, // intermediate results
        cache: AstHashMap<M, R>, // cached values
        args: Vec<R>, // temporary, for storing arguments when creating `View`
    }

    #[derive(Clone)]
    enum Task<AST> {
        // must be an application of `n` arguments.
        // Pops `n+1` from `res`, pushes one value onto `res`.
        Exit(AST),
        Enter(AST), // will eventually push one value onto `res`
    }

    impl<'a,M,R> State<'a,M,R> where M: Manager, R: Clone, M::Sym : Clone {
        /// New state
        pub fn new(m: &'a mut M) -> Self {
            let map: AstHashMap<M,R> = AstHashMap::new();
            State {m, st: State0::new(map), }
        }

        /// Iterate over the given AST `t`, calling `f` on every subterm once.
        ///
        /// `f` is passed:
        /// - the manager itself
        /// - the original subterm
        /// - a view of the original subterm where its own immediate subterms
        ///   have been transformed by `f` already
        pub fn map<F>(&mut self, t: M::AST, mut f: F) -> R
            where F: FnMut(&mut M, &M::AST, View<M::Sym,R>) -> R
        {
            self.st.tasks.push(Task::Enter(t));
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
                                        let view = View::Const(s.clone());
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

    impl<M: Manager, R> State0<M,R> {
        fn new(map: AstHashMap<M, R>) -> Self {
            Self {
                cache: map, tasks: vec!(),
                res: vec!(), args: vec!(),
            }
        }
    }
}
