
//! AST defined as a `u32`.
//!
//! This AST is sufficient for any manager that will store terms in a `Vec`,
//! and allows us to define common types for Sets and Maps.

use {
    std::u32, crate::ast,
};

/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST(u32);

impl AST {
    /// A value of type AST. Only ever use to fill array, do not access.
    pub const SENTINEL : AST = AST(u32::MAX);

    /// Access the underlying integer.
    #[inline(always)]
    pub fn idx(&self) -> u32 { self.0 }
}

impl ast::HasID for AST {
    fn get_id(&self) -> Option<usize> { Some(self.0 as usize) }
}

pub mod manager_util {
    use super::*;

    /// Create a new AST value.
    ///
    /// *NOTE*: this should only be used when implementing AST managers.
    #[inline(always)]
    pub fn ast_from_u32(x: u32) -> AST {
        assert_ne!(x, u32::MAX, "overflow in AST creation");
        AST(x)
    }
}

/// Dense set of terms.
pub struct DenseSet(::bit_set::BitSet);

mod dense_set {
    use super::*;

    impl ast::AstSet<AST> for DenseSet {
        /// New bitset
        #[inline(always)]
        fn new() -> Self { DenseSet::new() }

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
    impl ast::DenseSet<AST> for DenseSet {}
    
    impl DenseSet {
        /// Shrink internal storage.
        pub fn shrink_to_fit(&mut self) { self.0.shrink_to_fit() }

        /// New set
        #[inline(always)]
        pub fn new() -> Self { DenseSet(::bit_set::BitSet::new()) }
    }
}

/// A hashmap whose keys are AST nodes
pub type HashMap<V> = ast::HashMap<AST, V>;

/// A hashset whose keys are AST nodes
pub type HashSet = ast::HashSet<AST>;

pub type SparseSet = HashSet;

/// Compute size of the term, seen as a tree.
pub fn ast_size_tree<M:ast::Manager<AST=AST>>(m: &mut M, t: &AST) -> usize {
    ast::map_dag(
        m, t,
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
    use self::ast::DenseMap as AstDenseMap;

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
        #[inline(always)]
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
        /// New dense map.
        pub fn new(sentinel: V) -> Self {
            DenseMap {sentinel, mem: BitSet::new(), vec: Vec::new(), len: 0, }
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

    impl<V : Clone> AstDenseMap<AST, V> for DenseMap<V> {
        fn new(v: V) -> Self { DenseMap::new(v) }

        #[inline(always)]
        fn get_unchecked(&self, t: &AST) -> &V {
            debug_assert!(self.mem.contains(t.0 as usize));
            &self.vec[t.0 as usize]
        }

        #[inline(always)]
        fn get_mut_unchecked(&mut self, t: &AST) -> &mut V {
            debug_assert!(self.mem.contains(t.0 as usize));
            &mut self.vec[t.0 as usize]
        }
    }

    impl<V: Clone> std::ops::Index<AST> for DenseMap<V> {
        type Output = V;
        #[inline(always)]
        fn index(&self, id: AST) -> &Self::Output {
            self.get_unchecked(&id)
        }
    }

    impl<V: Clone> std::ops::IndexMut<AST> for DenseMap<V> {
        #[inline(always)]
        fn index_mut(&mut self, id: AST) -> &mut Self::Output {
            self.get_mut_unchecked(&id)
        }
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
