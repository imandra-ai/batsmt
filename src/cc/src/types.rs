
use {
    smallvec::SmallVec,
};

pub use batsmt_theory::{Ctx, BoolLit, Actions, };

/// a small vector of `T`
pub type SVec<T> = SmallVec<[T; 3]>;

/// Builtin symbols required by the congruence closure
#[derive(Debug,Clone)]
pub struct Builtins<AST:Clone> {
    pub true_: AST,
    pub false_: AST,
    pub not_: AST,
    pub eq: AST,
    pub distinct: AST,
}
