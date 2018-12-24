
extern crate bit_set;
extern crate fxhash;

pub mod ast;
pub mod gc;
pub mod backtrack;
pub mod shared;
pub mod ast_u32;

pub use crate::{
  backtrack::{Stack as BacktrackStack,Backtrackable},
  ast::{
      Manager,
      View as AstView,
      AstSet, DenseSet, SparseSet,
      AstMap, DenseMap, SparseMap,
      WithDenseSet, WithDenseMap, WithSparseSet, WithSparseMap,
  },
  gc::GC,
  shared::{Shared,SharedRef,SharedRefMut},
};

