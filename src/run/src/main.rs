
// A test binary

extern crate env_logger;
extern crate batsmt_core;
extern crate batsmt_cc;
extern crate batsmt_parser;
extern crate fxhash;
#[macro_use] extern crate log;

use {
    std::{env,fs,error::Error},
    batsmt_core::{ast,AST,StrSymbol},
    batsmt_cc::CC,
    batsmt_parser::{self as parser, simple_ast},
    fxhash::FxHashMap,
};

/* TODO: parse into manager
type M = ast::Manager<StrSymbol>;

/// AST builder for the parser
struct AstBuilder {
    m: M,
    bool_: AST,
    true_: AST,
    false_: AST,
    eq: AST,
    and_: AST,
    or_: AST,
    imply_: AST,
    sorts: FxHashMap<String, (AST, u8)>,
    funs: FxHashMap<String, (AST, Vec<AST>, AST)>, // sort
}

mod ast_builder {
    use super::*;

    impl AstBuilder {
        fn new(m: &M) -> Self { Self { m: m.clone() } }
    }

    impl parser::SortBuilder for AstBuilder {
        type Sort = AST;

        fn get_bool(&self) -> AST { self.bool_ }

        fn declare_sort(&mut self, s: String, arity: u8) -> AST {
            debug!("declare sort {:?} arity {}", &s, arity);
            if self.sorts.contains_key(&s) {
                panic!("sort {:?} already declared", &s);
            } else {
                let ast = self.m.get_mut().mk_str(&s);
                self.sorts.insert(s, (ast, arity));
                ast
            }
        }
    }

    impl parser::TermBuilder for AstBuilder {
        type Term = AST;
        type Fun = AST;

        fn var

        fn get_builtin(&self, op: parser::BuiltinOp) -> AST {
            use parser::BuiltinOp::*;
            match op {
                Imply => self.imply_,
                // TODO
            }
        }

    }

}
*/

fn main() -> Result<(), Box<Error>> {
    env_logger::init();

    let mut m : ast::Manager<StrSymbol> = ast::Manager::new();

    // TODO: use proper builder when ready
    // let mut b = AstBuilder::new(&m);
    let mut b = simple_ast::Builder::new();

    // TODO: create a Solver parametrized by the CC

    // parse
    let stmts = {
        let mut args = env::args();
        match args.skip(1).next() {
            None => {
                info!("parse stdin");
                parser::parse_stdin(&mut b)?
            },
            Some(file) => {
                info!("parse file {:?}", file);
                let file = fs::File::open(file)?;
                parser::parse(&mut b, file)?
            },
        }
    };

    info!("parsed {} statements", stmts.len());
    for s in &stmts {
        println!("parsed statement {}", s);
    }

    Ok(())
}
