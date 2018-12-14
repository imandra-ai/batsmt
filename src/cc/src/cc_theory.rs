
//! Theory built on the congruence closure

use {
    batsmt_core::{self as core,ast::{self,AST},symbol::Symbol, backtrack},
    batsmt_solver::{theory,theory::BLit},
    batsmt_pretty as pp,
    crate::{Builtins,cc::CC,naive_cc::NaiveCC,CCInterface,Conflict,PropagationSet},
};

// TODO: notion of micro theory should come here

type M<S> = ast::Manager<S>;

// pick implementation of CC
enum CCI<S:Symbol> {
    Fast(CC<S>),
    Slow(NaiveCC<S>),
}

mod cci {
    use super::*;

    // make analysis by case on CCI easier
    macro_rules! fun_case {
        ( $f:ident, SELF [ $( $arg:ident $ty:ty ),* ], $ret:ty, $c:ident, $rhs: expr ) => {
            fn $f(&self, $( $arg: $ty ),* ) -> $ret {
                match self {
                    CCI::Fast($c) => $rhs,
                    CCI::Slow($c) => $rhs,
                }
            }
        };

        ( $f:ident, MUT [ $( $arg:ident $ty:ty ),* ], $ret:ty, $c:ident, $rhs: expr ) => {
            fn $f(&mut self, $( $arg: $ty ),*) -> $ret {
                match self {
                    CCI::Fast($c) => $rhs,
                    CCI::Slow($c) => $rhs,
                }
            }
        };
    }

    impl<S:Symbol> backtrack::Backtrackable for CCI<S> {
        fun_case!(push_level, MUT [], (), c, c.push_level());
        fun_case!(pop_levels, MUT [n usize], (), c, c.push_level());
        fun_case!(n_levels, SELF [], usize, c, c.n_levels());
    }

    impl<S:Symbol> CCInterface for CCI<S> {
        fun_case!(merge, MUT [t1 AST, t2 AST, lit BLit], (), c, c.merge(t1,t2,lit));
        fun_case!(distinct, MUT [ts &[AST], lit BLit], (), c, c.distinct(ts,lit));
        fun_case!(check, MUT [], Result<&PropagationSet,Conflict>, c, c.check());
    }
}

/// A theory built on top of a congruence closure.
pub struct CCTheory<S:Symbol>{
    m: M<S>,
    builtins: Builtins,
    cc: CCI<S>,
}

mod cc_theory {
    use super::*;

    // TODO: use std::env to do it at runtime?
    // this determines which implementation to use
    const USE_FAST : bool = false;

    impl<S:Symbol> CCTheory<S> {
        /// Build a new theory for equality, based on congruence closure.
        pub fn new(m: &M<S>, b: Builtins) -> Self {
            let cc = {
                if USE_FAST {
                    debug!("use fast CC");
                    CCI::Fast(CC::new(&m, b.clone()))
                } else {
                    debug!("use slow CC");
                    CCI::Slow(NaiveCC::new(&m, b.clone()))
                }
            };
            Self { builtins: b, m: m.clone(), cc }
        }
    }

    impl<S:Symbol> core::backtrack::Backtrackable for CCTheory<S> {
        fn push_level(&mut self) { self.cc.push_level() }
        fn pop_levels(&mut self, n:usize) { self.cc.pop_levels(n) }
        fn n_levels(&self) -> usize { self.cc.n_levels() }
    }
}

// what do to from a tuple
enum Op<'a> {
    Eq(AST,AST),
    Distinct(&'a [AST]), // more than 2 elements
}

impl<S:Symbol> theory::Theory<S> for CCTheory<S> {
    fn final_check(&mut self, acts: &mut theory::Actions, trail: &theory::Trail) {
        let mut do_sth = false;

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
                            Op::Eq(args[0], args[1])
                        } else {
                            Op::Eq(ast, self.builtins.false_) // `(a=b)=false`
                        }
                    },
                    ast::View::App {f, args} if f == self.builtins.distinct => {
                        if !sign {
                            panic!("cannot handle negative `distinct`")
                        };
                        Op::Distinct(args)
                    },
                    _ if sign => {
                        Op::Eq(ast, self.builtins.true_)
                    },
                    _ => {
                        Op::Eq(ast, self.builtins.false_)
                    }
                }
            };

            do_sth = true;

            trace!("cc: op {}", pp::display(self.m.pp(&op)));
            match op {
                Op::Eq(a,b) => {
                    self.cc.merge(a,b,lit)
                },
                Op::Distinct(_) => unimplemented!("`distinct` is not supported"),
            }
        }

        // check CC's satisfiability
        if do_sth {
            match self.cc.check() {
                Ok(props) if props.len() == 0 => (), // trivial!
                Ok(props) => {
                    for _c in props.iter() {
                        unimplemented!("cannot do propagation yet");
                        // TODO: convert into clause? OR directly add this to batsat?
                        // TODO: `acts` should take `add_propagation(TheoryList, I: Iterator…)`
                        //       and make a lemma out of it, or use better API
                        // acts.add_bool_lemma(c);
                    }
                },
                Err(c) => {
                    acts.raise_conflict_iter(c.0.iter())
                }
            }
        }
    }
}

mod op {
    use super::*;

    impl<'a> ast::PrettyM for Op<'a> {
        fn pp_m<S:Symbol>(&self, m: &M<S>, ctx: &mut pp::Ctx) {
            match self {
                Op::Eq(a,b) => {
                    ctx.sexp(|ctx| {
                        ctx.str("=").space().array(pp::space(),&[m.pp(a), m.pp(b)]);
                    });
                },
                Op::Distinct(args) => {
                    ctx.sexp(|ctx| {
                        ctx.str("distinct").space().iter(pp::space(), args.iter().map(|t| m.pp(t)));
                    });
                },
            }
        }
    }
}


