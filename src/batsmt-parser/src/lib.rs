
extern crate fxhash;
#[macro_use] extern crate log;

pub mod types;
pub mod parser;

pub use types::{Statement,TermBuilder,SortBuilder};
pub use parser::{parse,parse_stdin,parse_str,Error,Result};

