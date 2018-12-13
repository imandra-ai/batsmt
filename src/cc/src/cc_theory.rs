
//! Theory built on the congruence closure

use {
    batsmt_core::{self as core,theory,ast::{self,AST},symbol::Symbol},
    crate::cc::{CC,BLit},
};

// TODO: notion of micro theory should come here

// TODO: Builtins structure with true,false,bool,eq,distinct

#[derive(Debug,Clone)]
pub struct Builtins {
    pub true_: AST,
    pub false_: AST,
    pub eq: AST,
    pub distinct: AST,
}

type M<S> = ast::Manager<S>;

/// A theory built on top of a congruence closure.
pub struct CCTheory<S:Symbol>{
    m: M<S>,
    builtins: Builtins,
    cc: CC<S>,
}

impl<S:Symbol> CCTheory<S> {
    pub fn new(m: &M<S>, b: Builtins) -> Self {
        let cc = CC::new(&m);
        Self { builtins: b, m: m.clone(), cc }
    }
}

impl<S:Symbol> core::backtrack::Backtrackable for CCTheory<S> {
    fn push_level(&mut self) { self.cc.push_level() }
    fn pop_levels(&mut self, n:usize) { self.cc.pop_levels(n) }
    fn n_levels(&self) -> usize { self.cc.n_levels() }
}

impl<S:Symbol> theory::Theory<S> for CCTheory<S> {
    fn final_check(&mut self, acts: &mut theory::Actions, trail: &theory::Trail) {
        let mut do_sth = false;

        // what do to from a tuple
        enum Op<'a> {
            Eqn(AST,AST),
            Distinct(&'a [AST])
        };

        // local borrow of AST manager
        let m = self.m.get();

        // update congruence closure
        for (ast,sign,lit) in trail.iter() {
            // convert `ast is {true,false}` into
            let op = {
                match m.view(ast) {
                    ast::View::App {f, args} if f == self.builtins.eq => {
                        assert_eq!(2,args.len());
                        if sign {
                            Op::Eqn(args[0], args[1])
                        } else {
                            Op::Distinct(args)
                        }
                    },
                    ast::View::App {f, args} if f == self.builtins.distinct => {
                        if !sign {
                            panic!("cannot handle negative `distinct`")
                        };
                        Op::Distinct(args)
                    },
                    _ if sign => {
                        Op::Eqn(ast, self.builtins.true_)
                    },
                    _ => {
                        Op::Eqn(ast, self.builtins.false_)
                    }
                }
            };

            do_sth = true;

            // now add to CC
            unimplemented!() // FIXME
        }

        // check CC's satisfiability
        if do_sth {
            match self.cc.check() {
                Ok(props) => panic!(), // FIXME
                Err(c) => panic!(), // FIXME
            }
        }
    }
}


