
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
};

fn main() -> Result<(), Box<Error>> {
    env_logger::init();

    let mut _m : ast::Manager<StrSymbol> = ast::Manager::new();
    // TODO: use real AST here?
    let mut b = simple_ast::Builder::new();

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
