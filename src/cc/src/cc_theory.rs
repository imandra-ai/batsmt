
//! Theory built on the congruence closure

use {
    batsmt_core::{self as core,ast::{self,AST},symbol::Symbol},
    batsmt_theory::{self as theory, BoolLit},
    batsmt_pretty as pp,
    crate::{Builtins,CCInterface},
};

#[allow(unused_imports)]
use crate::{naive_cc::NaiveCC,cc::CC};

// TODO: notion of micro theory should come here

type M<S> = ast::Manager<S>;

#[cfg(feature="naive")]
type CCI<S,B> = NaiveCC<S,B>;

#[cfg(not(feature="naive"))]
type CCI<S,B> = CC<S,B>;

/// A theory built on top of a congruence closure.
pub struct CCTheory<S:Symbol,B: BoolLit>{
    m: M<S>,
    builtins: Builtins,
    cc: CCI<S,B>,
}

impl<S:Symbol,B:BoolLit> CCTheory<S,B> {
    /// Build a new theory for equality, based on congruence closure.
    pub fn new(m: &M<S>, b: Builtins) -> Self {
        let cc = CCI::new(&m, b.clone());
        debug!("use {}", cc.impl_descr());
        Self { builtins: b, m: m.clone(), cc }
    }

    fn check(
        &mut self, partial: bool, acts: &mut theory::Actions<B>,
        trail: &theory::Trail<B>
    ) -> bool {
        if partial && ! CCI::<S,B>::has_partial_check() {
            return false; // doesn't handle partial checks
        }

        debug!("cc.{}-check", if partial { "partial" } else { "final" });
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

            trace!("process-op {} (expl {:?})", self.m.pp(&op), lit);
            match op {
                Op::Eq(a,b) => {
                    self.cc.merge(a,b,lit)
                },
                Op::Distinct(_) => unimplemented!("`distinct` is not supported"),
            }
        }

        // check CC's satisfiability
        if do_sth {
            let res = if partial {
                if let Some(r) = self.cc.partial_check() {
                    r
                } else {
                    return false // didn't do anything
                }
            } else {
                self.cc.final_check()
            };
            match res {
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
                    let costly = true;
                    let iter = c.0.iter().map(|b| theory::TheoryLit::B(*b));
                    acts.raise_conflict_iter(iter, costly)
                }
            };
        }
        true
    }
}

impl<S:Symbol,B:BoolLit> core::backtrack::Backtrackable for CCTheory<S,B> {
    fn push_level(&mut self) { self.cc.push_level() }
    fn pop_levels(&mut self, n:usize) { self.cc.pop_levels(n) }
    fn n_levels(&self) -> usize { self.cc.n_levels() }
}

// what do to from a tuple
enum Op<'a> {
    Eq(AST,AST),
    Distinct(&'a [AST]), // more than 2 elements
}

impl<S:Symbol, B:BoolLit> theory::Theory<S,B> for CCTheory<S,B> {
    fn final_check(&mut self, acts: &mut theory::Actions<B>, trail: &theory::Trail<B>) {
        self.check(false, acts, trail);
    }

    fn partial_check(&mut self, acts: &mut theory::Actions<B>, trail: &theory::Trail<B>) -> bool {
        self.check(true, acts, trail)
    }

    fn add_literal(&mut self, t: AST, lit: B) {
        self.cc.add_literal(t,lit);
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


