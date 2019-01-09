
//! Theory built on the congruence closure

use {
    batsmt_core::{ast::{self, }, backtrack, },
    batsmt_theory::{self as theory},
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
    pub fn new(m: &mut C, b: Builtins<C::AST>) -> Self {
        let cc = CCI::new(m, b.clone());
        debug!("use {}", CCI::<C>::impl_descr());
        Self { builtins: b, cc }
    }

    /// Add trail to the congruence closure, returns `true` if anything was added
    fn add_trail_to_cc(&mut self, m: &C, trail: &theory::Trail<C>) -> bool {
        let mut done_sth = false;

        // update congruence closure
        for (ast,sign,lit) in trail.iter() {
            // convert `ast is {true,false}` into a merge/distinct op
            match m.view(&ast) {
                ast::View::App {f, args} if f == self.builtins.eq => {
                    assert_eq!(2,args.len());
                    if sign {
                        self.cc.merge(m, args[0], args[1], lit);
                    } else {
                        // `(a=b)=false`
                        self.cc.merge(m, ast, self.builtins.false_, lit);
                    }
                },
                ast::View::App {f, args} if f == self.builtins.distinct => {
                    if !sign {
                        panic!("cannot handle negative `distinct`")
                    };
                    self.cc.distinct(m, args, lit)
                },
                _ if sign => {
                    self.cc.merge(m, ast, self.builtins.true_, lit)
                },
                _ => {
                    self.cc.merge(m, ast, self.builtins.false_, lit)
                }
            }

            done_sth = true;
        }
        done_sth
    }
}

impl<C:Ctx> backtrack::Backtrackable<C> for CCTheory<C> {
    fn push_level(&mut self, c: &mut C) { self.cc.push_level(c) }
    fn pop_levels(&mut self, c: &mut C, n:usize) { self.cc.pop_levels(c, n) }
    fn n_levels(&self) -> usize { self.cc.n_levels() }
}


fn act_propagate<C:Ctx>(acts: &mut theory::Actions<C>, props: &PropagationSet<C::B>) {
    if props.len() > 0 {
        for p in props.iter() {
            acts.propagate(p)
        }
    }
}

fn act_conflict<C:Ctx>(acts: &mut theory::Actions<C>, c: Conflict<C::B>) {
    let costly = true;
    // need to add negation
    let iter = c.0.iter().map(|b| !theory::TheoryLit::B(*b));
    acts.raise_conflict_iter(iter, costly)
}

impl<C:Ctx> theory::Theory<C> for CCTheory<C> {
    fn final_check(
        &mut self, ctx: &mut C,
        acts: &mut theory::Actions<C>, trail: &theory::Trail<C>
    ) {
        debug!("cc.final-check");
        self.add_trail_to_cc(ctx, trail);
        let res = self.cc.final_check(ctx);

        match res {
            Ok(props) => act_propagate(acts, props),
            Err(cls) => act_conflict(acts, cls),
        };
    }

    fn partial_check(
        &mut self, ctx: &mut C,
        acts: &mut theory::Actions<C>, trail: &theory::Trail<C>
    ) {
        if ! CCI::<C>::has_partial_check() {
            return; // doesn't handle partial checks
        }
        debug!("cc.partial-check");
        trace!("trail: {:?}", trail.as_slice());

        // TODO: shouldn't this shortcut be done in main solver already?
        let do_sth = self.add_trail_to_cc(ctx, trail);
        if !do_sth {
            return; // nothing new
        }
        let res = self.cc.partial_check(ctx);

        match res {
            Ok(props) => act_propagate(acts, props),
            Err(cls) => act_conflict(acts, cls),
        };
    }

    fn has_partial_check() -> bool {
        CCI::<C>::has_partial_check()
    }

    fn add_literal(&mut self, ctx: &C, t: C::AST, lit: C::B) {
        self.cc.add_literal(ctx, t,lit);
    }

    fn explain_propagation(&mut self, m: &C, t: C::AST, sign: bool, _p: C::B) -> &[C::B] {
        // what does `t=sign` correspond to?
        trace!("explain-prop {} sign={} (lit {:?})", ast::pp(m,&t), sign, _p);
        match m.view(&t) {
            ast::View::App {f, args} if f == self.builtins.eq => {
                assert_eq!(2,args.len());
                if sign {
                    self.cc.explain_merge(m, args[0], args[1])
                } else {
                    // `(a=b)=false`
                    self.cc.explain_merge(m, t, self.builtins.false_)
                }
            },
            ast::View::App {f, args:_} if f == self.builtins.distinct => {
                panic!("cannot explain propagations of `distinct`")
            },
            _ if sign => {
                self.cc.explain_merge(m, t, self.builtins.true_)
            },
            _ => {
                self.cc.explain_merge(m, t, self.builtins.false_)
            }
        }
    }
}
