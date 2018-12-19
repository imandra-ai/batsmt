
//! General notion of Theory

#[macro_use] extern crate log;

mod types;

pub use crate::types::{
  Theory, TheoryLit, TheoryClause, TheoryClauseSet, TheoryClauseRef,
  Actions, ActState, Trail, BoolLit,
  int_lit::Lit as IntLit,
};

