
//! Theory built on the congruence closure

use {
    batsmt_core::{self as core,ast::{self,AST},symbol::Symbol},
    batsmt_theory::{self as theory, BoolLit},
    crate::{Builtins,CCInterface,Check,PropagationSet,Conflict},
};

#[allow(unused_imports)]
use crate::{naive_cc::NaiveCC,cc::CC};

// TODO: notion of micro theory should come here

type M<S> = ast::Manager<S>;

#[cfg(feature="naive")]
type CCI<S,B> = NaiveCC<S,B>;

#[cfg(not(feature="naive"))]
type CCI<S,B> = CC<S,B>;

type CCICheck<S,B> = <CCI<S,B> as CCInterface<B>>::Checker;

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

    /// Get checker, add trail to it
    fn checker_with_trail(&mut self, trail: &theory::Trail<B>) -> (bool, &mut CCICheck<S,B>)  {
        let mut done_sth = false;
        let checker = self.cc.checker();

        // update congruence closure
        let m = self.m.get();
        for (ast,sign,lit) in trail.iter() {
            // convert `ast is {true,false}` into a merge/distinct op
            match m.view(ast) {
                ast::View::App {f, args} if f == self.builtins.eq => {
                    assert_eq!(2,args.len());
                    if sign {
                        checker.merge(args[0], args[1], lit);
                    } else {
                        // `(a=b)=false`
                        checker.merge(ast, self.builtins.false_, lit);
                    }
                },
                ast::View::App {f, args} if f == self.builtins.distinct => {
                    if !sign {
                        panic!("cannot handle negative `distinct`")
                    };
                    checker.distinct(args, lit)
                },
                _ if sign => {
                    checker.merge(ast, self.builtins.true_, lit)
                },
                _ => {
                    checker.merge(ast, self.builtins.false_, lit)
                }
            }

            done_sth = true;
        }
        (done_sth,checker)
    }
}

impl<S:Symbol,B:BoolLit> core::backtrack::Backtrackable for CCTheory<S,B> {
    fn push_level(&mut self) { self.cc.push_level() }
    fn pop_levels(&mut self, n:usize) { self.cc.pop_levels(n) }
    fn n_levels(&self) -> usize { self.cc.n_levels() }
}


fn act_propagate<B:BoolLit>(acts: &mut theory::Actions<B>, props: &PropagationSet<B>) {
    if props.len() > 0 {
        for _c in props.iter() {
            break;
            // TODO: pass to the Actions directly
            // TODO: `acts` should take `add_propagation(TheoryList, I: Iterator…)`
            //       and make a lemma out of it, or use better API
            // acts.add_bool_lemma(c);
        }
    }
}

fn act_conflict<B:BoolLit>(acts: &mut theory::Actions<B>, c: Conflict<B>) {
    let costly = true;
    let iter = c.0.iter().map(|b| theory::TheoryLit::B(*b));
    acts.raise_conflict_iter(iter, costly)
}

impl<S:Symbol, B:BoolLit> theory::Theory<S,B> for CCTheory<S,B> {
    fn final_check(&mut self, acts: &mut theory::Actions<B>, trail: &theory::Trail<B>) {
        debug!("cc.final-check");
        let (_,checker) = self.checker_with_trail(trail);
        let res = checker.final_check();

        match res {
            Ok(props) => act_propagate(acts, props),
            Err(c) => act_conflict(acts, c),
        };
    }

    fn partial_check(&mut self, acts: &mut theory::Actions<B>, trail: &theory::Trail<B>) {
        if ! CCI::<S,B>::has_partial_check() {
            return; // doesn't handle partial checks
        }
        debug!("cc.partial-check");

        let (do_sth,checker) = self.checker_with_trail(trail);
        if !do_sth {
            return; // nothing new
        }
        let res = checker.partial_check();

        match res {
            Ok(props) => act_propagate(acts, props),
            Err(c) => act_conflict(acts, c),
        };
    }

    fn has_partial_check() -> bool {
        CCI::<S,B>::has_partial_check()
    }

    fn add_literal(&mut self, t: AST, lit: B) {
        self.cc.add_literal(t,lit);
    }
}
