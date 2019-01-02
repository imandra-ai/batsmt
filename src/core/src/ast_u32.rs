
//! AST defined as a `u32`.
//!
//! This AST is sufficient for any manager that will store terms in a `Vec`,
//! and allows us to define common types for Sets and Maps.

use {
    std::u32, crate::ast::{self, View, },
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
pub fn ast_size_tree<M:ManagerU32>(m: &mut M, t: &AST) -> usize {
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

    impl<V : Clone> ast::DenseMap<AST, V> for DenseMap<V> {
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

        #[inline]
        fn get2(&mut self, t1: AST, t2: AST) -> (&mut V, &mut V) {
            let t1 = t1.0 as usize;
            let t2 = t2.0 as usize;

            assert_ne!(t1, t2, "get2: aliased access");
            debug_assert!(self.mem.contains(t1) && self.mem.contains(t2),
                          "get2: doesn't contain one of the keys");

            let ref1 = (&mut self.vec[t1]) as *mut V;
            let ref2 = (&mut self.vec[t2]) as *mut V;
            // this is correct because t1 != t2, so the pointers are disjoint.
            unsafe { (&mut* ref1, &mut *ref2) }
        }
    }
}

/// A refinement of `Manager` where AST is the u32 AST.
pub trait ManagerU32 : ast::Manager<AST=AST> {}

// auto impl
impl<M> ManagerU32 for M where M: ast::Manager<AST=AST> {}

impl<M, V:Clone> ast::WithSparseMap<AST,V> for M where M: ManagerU32 {
    type SparseMap = ast::HashMap<AST,V>;
    fn new_sparse_map() -> Self::SparseMap { ast::SparseMap::new() }
}

impl<M, V:Clone> ast::WithDenseMap<AST,V> for M where M: ManagerU32 {
    type DenseMap = DenseMap<V>;
    fn new_dense_map(v: V) -> Self::DenseMap { DenseMap::new(v) }
}

impl<M> ast::WithSparseSet<AST> for M where M: ManagerU32 {
    type SparseSet = ast::HashSet<AST>;
    fn new_sparse_set() -> Self::SparseSet { SparseSet::new() }
}


impl<M> ast::WithDenseSet<AST> for M where M: ManagerU32 {
    type DenseSet = DenseSet;
    fn new_dense_set() -> Self::DenseSet { DenseSet::new() }
}
