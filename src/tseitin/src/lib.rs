
//! Tseitin Transformation
//!
//! See [wikipedia](https://en.wikipedia.org/wiki/Tseytin_transformation)
//! for a primer.

#[macro_use] extern crate log;

use {
    batsmt_core::{
        ast_u32::{self, AST, }, gc,
        ast::{self, View, iter_dag::State as AstIter},
    },
    batsmt_theory::{
        TheoryLit, TheoryClauseSet, TheoryClauseRef,
        LitMap, Ctx, },
};

/// Main state for the Tseitin transformation.
///
/// The state remembers which formulas have been translated to clauses already.
#[derive(Clone)]
pub struct Tseitin<C:Ctx> {
    b: Builtins,
    iter: AstIter<AST, ast_u32::HashSet>, // to traverse subterms
    tmp: Vec<TheoryLit<C>>, // temp clause
    tmp2: Vec<TheoryLit<C>>, // temp clause
    tmp_ast: Vec<AST>, // for arguments
    cs: TheoryClauseSet<C>, // clauses
}

/// The set of builtins we need to preprocess formulas.
#[derive(Clone,Debug)]
pub struct Builtins {
    pub true_: AST,
    pub false_: AST,
    pub not_: AST,
    pub and_: AST,
    pub or_: AST,
    pub imply_: AST,
    pub distinct: AST,
    pub eq: AST,
}

impl Builtins {
    // connective?
    fn is_conn(&self, t: &AST) -> bool {
        t == &self.not_ ||
        t == &self.and_ ||
        t == &self.or_ ||
        t == &self.imply_ ||
        t == &self.distinct ||
        t == &self.eq
    }

}

/// Temporary structure
struct LitMapB<'a, C:Ctx, LM: LitMap<C::B>> {
    m: &'a mut C,
    lit_map: &'a mut LM,
    b: &'a Builtins,
}

impl<'a,C,LM> LitMapB<'a,C,LM>
    where C: Ctx, LM:LitMap<C::B>
{
    /// Map `t,sign` to either a theory literal, or a lazy pure boolean literal
    fn term_to_lit(&mut self, t: &AST) -> TheoryLit<C> {
        let (t,sign) = self.lit_map.unfold_not(self.m,t, true);
        let b = &self.b;
        let view_t = self.m.view(&t);
        match view_t {
            View::App {f, args} => {
                if f == b.true_ || f == b.false_ {
                    TheoryLit::new_b(t, sign)
                } else if f == b.and_ || f == b.or_ || f == b.imply_ {
                    TheoryLit::new_b(t, sign)
                } else if f == b.distinct {
                    if args.len() == 2 {
                        // turn `distinct(a,b)` into `!(a=b)`
                        let t0 = args[0];
                        let t1 = args[1];
                        drop(view_t);
                        let eqn = self.m.mk_app(b.eq, &[t0, t1]);
                        ! TheoryLit::new_t(eqn, sign)
                    } else {
                        TheoryLit::new_b(t,sign) // encoded away
                    }
                } else {
                    // theory literal
                    TheoryLit::new_t(t, sign)
                }
            },
            View::Const(_) => TheoryLit::new_t(t,sign),
        }
    }
}

impl<C> Tseitin<C> where C: Ctx {
    /// Create a new Tseitin transformation
    pub fn new(b: Builtins) -> Self {
        Self {
            b,
            tmp: Vec::new(),
            tmp2: Vec::new(),
            tmp_ast: vec!(),
            iter: ast::iter_dag::new(),
            cs: TheoryClauseSet::new(),
        }
    }

    /// Clear internal caches.
    ///
    /// This means that formulas already defined in previous calls to
    /// `self.clauses(t)` will be re-defined if we meet them again.
    pub fn clear(&mut self) {
        self.iter.clear();
    }

    /// Simplify boolean expressions.
    pub fn simplify(&mut self, _m: &mut C, t: AST) -> AST {
        let u = t; // TODO
        debug!("tseitin.simplify\nfrom {}\nto {}", ast::pp(_m,&t), ast::pp(_m,&u));
        u
    }

    /// `tseitin.clauses(t)` turns the boolean term `t` into a set of clauses.
    ///
    /// The clauses define boolean connectives occurring inside `t`.
    /// ## params
    /// - `t` is the formula to normalize
    pub fn clauses<LM>(
        &mut self, m: &mut C, lit_map: &mut LM, t: AST
    ) -> impl Iterator<Item=TheoryClauseRef<C>>
        where LM: LitMap<C::B>
    {
        self.cs.clear();

        let Tseitin { b, tmp_ast, cs, tmp, tmp2, ..} = self;

        {
            // traverse `t` as a DAG
            self.iter.iter_mut(m, &t, |m, u| {
                // `u` is a subterm that has never been processed.
                let view_u = m.view(u);
                // TODO: only consider this if `f` is a connective?
                if let View::App{f, args} = view_u {
                    if ! b.is_conn(&f) {
                        return; // no need to copy arguments
                    }
                    tmp_ast.clear();
                    tmp_ast.extend_from_slice(args);
                    drop(view_u);

                    let args = &tmp_ast;
                    let mut lmb = LitMapB{lit_map, b, m};

                    // check if head symbol is a connective
                    if f == b.not_ {
                        debug_assert_eq!(1, args.len());
                        () // nothing to do here
                    } else if f == b.and_ {
                        // obtain literals for subterms of the `and` into `tmp`
                        tmp.clear();
                        for t in args.iter() {
                            tmp.push(lmb.term_to_lit(t));
                        }
                        let lit_and = lmb.term_to_lit(u); // pure bool
                        debug_assert!(lit_and.is_pure_bool());

                        // `lit_and => args[i]`
                        for &sub in tmp.iter() {
                            cs.push(&[!lit_and, sub]);
                        }
                        // `args[i] ==> lit_and`
                        {
                            tmp2.clear();
                            for &sub in tmp.iter() {
                                tmp2.push(!sub)
                            }
                            tmp2.push(lit_and);
                            cs.push(&tmp2);
                        }
                    } else if f == b.or_ {
                        // obtain literals for subterms of the `or` into `tmp`
                        tmp.clear();
                        for t in args.iter() {
                            tmp.push(lmb.term_to_lit(t));
                        }
                        let lit_or = lmb.term_to_lit(u); // pure bool
                        debug_assert!(lit_or.is_pure_bool());

                        // `args[i] => lit_or`
                        for &sub in tmp.iter() {
                            cs.push(&[!sub, lit_or]);
                        }
                        // `lit_or => ∨_i args[i]`
                        {
                            tmp2.clear();
                            tmp2.extend_from_slice(&tmp);
                            tmp2.push(!lit_or);
                            cs.push(&tmp2);
                        }
                    } else if f == b.imply_ {
                        // same as `or`, but all literals but the last are negated
                        assert!(args.len() >= 1);
                        tmp.clear();
                        {
                            let t_last = args[args.len()-1];
                            tmp.push(lmb.term_to_lit(&t_last));
                        }
                        for t in args[.. args.len()-1].iter() {
                            // negation here, LHS of implication
                            tmp.push(! lmb.term_to_lit(t));
                        }
                        let lit_or = lmb.term_to_lit(u); // pure bool
                        debug_assert!(lit_or.is_pure_bool());

                        // `args[i] => lit_or`
                        for &sub in tmp.iter() {
                            cs.push(&[!sub, lit_or]);
                        }
                        // `lit_or => ∨_i args[i]`
                        {
                            tmp2.clear();
                            tmp2.extend_from_slice(&tmp);
                            tmp2.push(!lit_or);
                            cs.push(&tmp2);
                        }
                    } else if f == b.distinct && args.len() <= 2 {
                        () // nop, encoded as equation
                    } else if f == b.distinct {
                        // eliminate `distinct` into a conjunction of O(n^2) dis-equations
                        let lit_distinct = lmb.term_to_lit(u);
                        drop(lmb);

                        // `∧i args[i]!=args[j] => distinct`
                        tmp.clear();
                        tmp.push(lit_distinct);

                        for i in 0 .. args.len()-1 {
                            let t_i = args[i];
                            for j in i+1 .. args.len() {
                                let t_j = args[j];
                                let eqn_i_j = {
                                    let t = m.mk_app(b.eq, &[t_i, t_j]);
                                    TheoryLit::new_t(t, true)
                                };

                                // `distinct => args[i]!=args[j]`
                                cs.push(&[!lit_distinct, !eqn_i_j]);

                                // enrich the big conjunction
                                tmp.push(eqn_i_j);
                            }
                        }

                        cs.push(&tmp);
                    }
                } else if u == &b.true_ {
                    cs.push(&[TheoryLit::new_b(*u, true)]) // clause [true]
                } else if u == &b.false_ {
                    // TODO: is this needed? `u` maps to `not true` anyway?
                    cs.push(&[TheoryLit::new_b(*u, false)]) // clause [¬false]
                }
            });
        }

        {
            // unit clause asserting that `t` is true
            let mut lmb = LitMapB{lit_map, b, m};
            let top_lit = lmb.term_to_lit(&t);
            self.cs.push(&[top_lit]);
        }

        self.cs.iter()
    }

}

impl<C> gc::HasInternalMemory for Tseitin<C> where C: Ctx {
    fn reclaim_unused_memory(&mut self) {
        self.tmp.shrink_to_fit();
        self.tmp2.shrink_to_fit();
        self.tmp_ast.shrink_to_fit();
        self.cs.reclaim_unused_memory();
        self.iter.reclaim_unused_memory();
    }
}

