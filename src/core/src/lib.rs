
extern crate bit_set;
extern crate fxhash;

pub mod ast;
pub mod gc;
pub mod backtrack;
pub mod shared;

pub use crate::{
  backtrack::{Stack as BacktrackStack,Backtrackable},
  ast::{
      Manager,
      AstHashMap,
      View as AstView,
      PrettyM,
  },
  gc::GC,
  shared::{Shared,SharedRef,SharedRefMut},
};

