
#[macro_use] extern crate log;

pub mod types;
pub mod parser;
pub mod simple_ast;

pub use crate::{
    types::{Atom,Statement,TermBuilder,SortBuilder,Op as BuiltinOp},
    parser::{parse,parse_stdin,parse_str,Error,Result},
};

