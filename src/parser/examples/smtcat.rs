
// A test binary that just parses smtlib and prints it

extern crate batsmt_logger;
extern crate batsmt_parser;
extern crate fxhash;
#[macro_use] extern crate log;

use {
    std::{env,fs,error::Error},
    batsmt_parser::{self as parser, simple_ast},
};

fn main() -> Result<(), Box<Error>> {
    batsmt_logger::init();

    let mut b = simple_ast::Builder::new();

    // parse
    let stmts = {
        let args = env::args();
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
