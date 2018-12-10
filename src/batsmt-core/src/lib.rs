
extern crate batsat;
extern crate bit_set;
extern crate fxhash;
#[macro_use] extern crate log;

pub mod ast;
pub mod gc;
pub mod symbol;
pub mod shared;
pub mod backtrack;

pub use {
  symbol::{Symbol,str::Sym as StrSymbol},
  backtrack::{BacktrackStack,Backtrackable,InvertibleOp},
  ast::{
      AST,
      Manager as AstManager,
      BitSet as AstBitSet,
      HashMap as AstHashMap,
      DenseMap as AstDenseMap,
      View as AstView
  },
  gc::GC,
  shared::SharedRef,
};

