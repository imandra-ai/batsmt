
// A test binary

extern crate env_logger;
extern crate batsmt_core;
extern crate batsmt_cc;
extern crate batsmt_parser;
extern crate batsmt_pretty;
extern crate fxhash;
#[macro_use] extern crate log;

mod ast_builder;
mod ast_printer;

use {
    std::{env,fs,error::Error},
    batsmt_core::{ast,StrSymbol},
    batsmt_cc::CC,
    batsmt_parser as parser,
    crate::ast_printer::PP,
};

fn main() -> Result<(), Box<Error>> {
    env_logger::init();

    let m : ast::Manager<StrSymbol> = ast::Manager::new();

    let mut b = ast_builder::AstBuilder::new(&m);

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
        println!("parsed statement {}", PP::new(&m, s.clone()));
    }

    Ok(())
}
