
// A test binary

#[macro_use] extern crate log;

mod ctx;
mod ast_builder;
mod ast_printer;

use {
    std::{env,fs,error::Error},
    batsmt_core::{Chrono, gc::HasInternalMemory, },
    batsmt_cc as cc,
    batsmt_parser::{self as parser, Statement},
    batsmt_tseitin::Tseitin,
    batsmt_solver as solver,
    batsmt_pretty::{self as pp, Pretty1},
};

pub use {
    crate::ctx::{M, Ctx, Builtins},
};

fn main() -> Result<(), Box<Error>> {
    batsmt_logger::init();
    let chrono = Chrono::new();

    let mut c = Ctx::new();

    // parse
    let stmts: Vec<_> = {
        let mut builder = ast_builder::AstBuilder::new(&mut c);
        let args = env::args();
        match args.skip(1).next() {
            None => {
                info!("parse stdin");
                parser::parse_stdin(&mut builder)?
            },
            Some(file) => {
                info!("parse file {:?}", file);
                let file = fs::File::open(file)?;
                parser::parse(&mut builder, file)?
            },
        }
    };

    info!("parsed {} statements (after {}s)", stmts.len(), chrono.as_f64());

    let th = cc::CCTheory::new(&mut c);
    let mut solver = solver::Solver::new(c.builtins(), th);

    // Tseitin transformation, to handle formulas
    let mut tseitin = Tseitin::new();

    for s in &stmts {
        debug!("parsed statement {}", pp::pp1(&c, s));

        // process statement
        match s {
            Statement::Assert(t) => {
                let t = tseitin.simplify(&mut c, *t);
                let cs = tseitin.clauses(&mut c, solver.lit_map_mut(), t);
                for clause in cs {
                    solver.add_clause(&mut c, clause);
                }
            },
            Statement::CheckSat => {
                tseitin.reclaim_unused_memory();
                let r = solver.solve(&mut c);
                println!("{:?}", r)
            },
            Statement::Exit => {
                info!("exit (after {}s)", chrono.as_f64());
                break;
            }
            _ => (),
        }
    }

    Ok(())
}
