
//! Abstraction over AST managers
//!
//! The core AST is parametrized by *symbols*, so that users can put
//! custom information in there.

use {
    std::{ hash::Hash, fmt::{self, Debug}, },
    fxhash::{FxHashMap, FxHashSet, },
    crate::gc,
    batsmt_pretty as pp,
};

/* TODO: remove
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
*/

/// An object that may have a unique integer ID.
pub trait HasID {
    fn get_id(&self) -> Option<usize> { None }
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

/* TODO: remove
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
*/

/// A view of an AST as a S-expression like object.
///
/// This is useful for printing.
pub enum SexpView<'a,Sym: fmt::Display,AST: HasID>  {
    Const(&'a Sym),
    App(&'a Sym, &'a [AST]),
    AppHO(&'a AST, &'a [AST]),
    List(&'a [AST]),
}

/// A context with a `sexp`-like view of terms.
pub trait CtxSexp {
    type Sym : fmt::Display;
    type AST : HasID;

    /// View terms as S-expressions.
    fn view_sexp(&self, t: &Self::AST) -> SexpView<Self::Sym, Self::AST>;
}

/// AST-pretty printer, using `f` to print symbols.
pub fn pp_ast<M>(m: &M, t: &M::AST, ctx: &mut pp::Ctx)
    where M: CtxSexp
{
    match m.view_sexp(t) {
        SexpView::Const(s) => {
            ctx.display(s);
        },
        SexpView::App(f0, args) if args.len() == 0 => {
            ctx.display(f0);
        },
        SexpView::App(f0, args) => {
            ctx.sexp(|ctx| {
                ctx.display(f0).space();
                for u in args.iter() {
                    ctx.space();
                    pp_ast(m, u, ctx);
                }
            });
        },
        SexpView::AppHO(f,args) if args.len() == 0 => {
            pp_ast(m, f, ctx);
        },
        SexpView::AppHO(f,args) => {
            ctx.sexp(|ctx| {
                pp_ast(m, f, ctx);
                for u in args.iter() {
                    ctx.space();
                    pp_ast(m, u, ctx);
                }
            });
        },
        SexpView::List(args) => {
            ctx.sexp(|ctx| {
                for (i,u) in args.iter().enumerate() {
                    if i>0 { ctx.space(); }
                    pp_ast(m, u, ctx);
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

/// An AST Set that is "sparse".
///
/// This indicates that it's probably based on some form of hashtable, and
/// therefore that access is slower than `DenseSet`, but that it's more
/// memory efficient when storing only a few elements.
pub trait SparseSet<AST:Clone> : AstSet<AST> {}

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
}

pub trait SparseMap<AST, V> : AstMap<AST, V> {
    /// Create a new empty sparse map.
    fn new() -> Self;
}

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

/// A notion of manager that can iterate over subterms represented as `AST`
pub trait HasIter<AST> {
    /// Iterate over the subterms of `t` exactly once.
    fn iter_dag<F>(&self, t: &Self::AST, f: F)
        where F: FnMut(&Self, &Self::AST);


    /// Compute size of the term, seen as a DAG.
    ///
    /// Each unique subterm is counted only once.
    fn size_dag<M>(m: &M, t: &M::AST) -> usize {
        let mut n = 0;
        iter_dag(m, t, |_,_| { n += 1 });
        n
    }
}
