
//! Theory built on the congruence closure

use {
    batsmt_core::{self as core,ast::{self, Manager}},
    batsmt_theory::{self as theory, BoolLit},
    crate::{Builtins, CCInterface, PropagationSet, Conflict, Ctx},
};

#[allow(unused_imports)]
use crate::{naive_cc::NaiveCC,cc::CC};

// TODO: notion of micro theory should come here

#[cfg(feature="naive")]
type CCI<M> = NaiveCC<M>;

#[cfg(not(feature="naive"))]
type CCI<M> = CC<M>;

/// A theory built on top of a congruence closure.
pub struct CCTheory<C:Ctx>{
    builtins: Builtins<C::AST>,
    cc: CCI<C>,
}

impl<C:Ctx> CCTheory<C> {
    /// Build a new theory for equality, based on congruence closure.
    pub fn new(m: &C::M, b: Builtins<C::AST>) -> Self {
        let cc = CCI::new(&m, b.clone());
        debug!("use {}", cc.impl_descr());
        Self { builtins: b, m: m.clone(), cc }
    }

    /// Add trail to the congruence closure, returns `true` if anything was added
    fn add_trail_to_cc(&mut self, trail: &theory::Trail<C>) -> bool {
        let mut done_sth = false;

        // update congruence closure
        let m = self.m.get();
        for (ast,sign,lit) in trail.iter() {
            // convert `ast is {true,false}` into a merge/distinct op
            match m.view(ast) {
                ast::View::App {f, args} if f == self.builtins.eq => {
                    assert_eq!(2,args.len());
                    if sign {
                        self.cc.merge(args[0], args[1], lit);
                    } else {
                        // `(a=b)=false`
                        self.cc.merge(ast, self.builtins.false_, lit);
                    }
                },
                ast::View::App {f, args} if f == self.builtins.distinct => {
                    if !sign {
                        panic!("cannot handle negative `distinct`")
                    };
                    self.cc.distinct(args, lit)
                },
                _ if sign => {
                    self.cc.merge(ast, self.builtins.true_, lit)
                },
                _ => {
                    self.cc.merge(ast, self.builtins.false_, lit)
                }
            }

            done_sth = true;
        }
        done_sth
    }
}

impl<C:Ctx> core::backtrack::Backtrackable for CCTheory<C> {
    fn push_level(&mut self) { self.cc.push_level() }
    fn pop_levels(&mut self, n:usize) { self.cc.pop_levels(n) }
    fn n_levels(&self) -> usize { self.cc.n_levels() }
}


fn act_propagate<C:Ctx>(acts: &mut theory::Actions<C>, props: &PropagationSet<C>) {
    if props.len() > 0 {
        for p in props.iter() {
            acts.propagate(p)
        }
    }
}

fn act_conflict<C:Ctx>(acts: &mut theory::Actions<C>, c: Conflict<C>) {
    let costly = true;
    let iter = c.0.iter().map(|b| theory::TheoryLit::B(*b));
    acts.raise_conflict_iter(iter, costly)
}

impl<C:Ctx> theory::Theory<C> for CCTheory<C> {
    fn final_check(&mut self, acts: &mut theory::Actions<C>, trail: &theory::Trail<C>) {
        debug!("cc.final-check");
        self.add_trail_to_cc(trail);
        let res = self.cc.final_check();

        match res {
            Ok(props) => act_propagate(acts, props),
            Err(c) => act_conflict(acts, c),
        };
    }

    fn partial_check(&mut self, acts: &mut theory::Actions<C>, trail: &theory::Trail<C>) {
        if ! CCI::<C>::has_partial_check() {
            return; // doesn't handle partial checks
        }
        debug!("cc.partial-check");

        // TODO: shouldn't this shortcut be done in main solver already?
        let do_sth = self.add_trail_to_cc(trail);
        if !do_sth {
            return; // nothing new
        }
        let res = self.cc.partial_check();

        match res {
            Ok(props) => act_propagate(acts, props),
            Err(c) => act_conflict(acts, c),
        };
    }

    fn has_partial_check() -> bool {
        CCI::<C>::has_partial_check()
    }

    fn add_literal(&mut self, t: C::AST, lit: C::B) {
        self.cc.add_literal(t,lit);
    }

    #[inline(always)]
    fn explain_propagation(&mut self, p: C::B) -> &[C::B] {
        self.cc.explain_propagation(p)
    }
}
