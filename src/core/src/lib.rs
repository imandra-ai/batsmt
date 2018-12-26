
extern crate bit_set;
extern crate fxhash;

pub mod ast;
pub mod gc;
pub mod backtrack;
pub mod shared;

pub use crate::{
  backtrack::{Stack as BacktrackStack,Backtrackable},
  ast::{
      Manager, ManagerCtx,
      View as AstView,
      AstSet, AstDenseSet, AstSparseSet,
      AstMap, AstDenseMap, AstSparseMap,
      WithDenseSet, WithDenseMap, WithSparseSet, WithSparseMap,
  },
  gc::GC,
  shared::{Shared,SharedRef,SharedRefMut},
};

