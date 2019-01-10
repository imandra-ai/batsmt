
//! Tseitin Transformation
//!
//! See [wikipedia](https://en.wikipedia.org/wiki/Tseytin_transformation)
//! for a primer.

#[macro_use] extern crate log;

use {
    batsmt_core::{
        ast_u32::{self, AST, }, gc,
        ast::{self, iter_dag::State as AstIter},
    },
    batsmt_theory::{
        self as theory, TheoryLit, TheoryClauseSet, TheoryClauseRef,
        LitMap, },
};

/// A boolean-centric view of formulas.
pub enum View<'a, AST> {
    Bool(bool),
    Not(AST),
    And(&'a [AST]),
    Or(&'a [AST]),
    Imply(&'a [AST]),
    Eq(AST,AST),
    Distinct(&'a [AST]),
    Atom(AST), // other
}

pub trait Ctx : theory::Ctx {
    /// How to view an AST.
    fn view_as_formula(&self, t: AST) -> View<AST>;

    /// Make an equality.
    fn mk_eq(&mut self, t: AST, u: AST) -> AST;
}

/// Main state for the Tseitin transformation.
///
/// The state remembers which formulas have been translated to clauses already.
#[derive(Clone)]
pub struct Tseitin<C:Ctx> {
    iter: AstIter<AST, ast_u32::HashSet>, // to traverse subterms
    tmp: Vec<TheoryLit<C>>, // temp clause
    tmp2: Vec<TheoryLit<C>>, // temp clause
    tmp_ast: Vec<AST>, // for arguments
    cs: TheoryClauseSet<C>, // clauses
}

/// Temporary structure
struct LitMapB<'a, C:Ctx, LM: LitMap<C::B>> {
    m: &'a mut C,
    lit_map: &'a mut LM,
}

impl<'a,C,LM> LitMapB<'a,C,LM>
    where C: Ctx, LM:LitMap<C::B>
{
    /// Map `t,sign` to either a theory literal, or a lazy pure boolean literal
    fn term_to_lit(&mut self, t: &AST) -> TheoryLit<C> {
        let (t,sign) = self.lit_map.unfold_not(self.m, t, true);
        let view_t = self.m.view_as_formula(t);
        match view_t {
            View::Bool(..) => {
                TheoryLit::new_b(t, sign)
            },
            View::And(..) | View::Or(..) | View::Imply(..) => {
                TheoryLit::new_b(t, sign)
            },
            View::Distinct(args) if args.len() == 2 => {
                // turn `distinct(a,b)` into `!(a=b)`
                let t0 = args[0];
                let t1 = args[1];
                drop(view_t);
                let eqn = self.m.mk_eq(t0, t1);
                ! TheoryLit::new_t(eqn, sign)
            },
            View::Distinct(..) => {
                TheoryLit::new_b(t,sign) // encoded away
            },
            View::Not(..) => panic!("should not have a negation"), // unfold-not
            View::Atom(..) | View::Eq(..) => {
                // theory literal
                TheoryLit::new_t(t, sign)
            },
        }
    }
}

impl<C> Tseitin<C> where C: Ctx {
    /// Create a new Tseitin transformation
    pub fn new() -> Self {
        Self {
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

        let Tseitin { tmp_ast: args, cs, tmp, tmp2, ..} = self;

        // traverse `t` as a DAG
        self.iter.iter_mut(m, &t, |m, u| {
            // `u` is a subterm that has never been processed.
            let view_u = m.view_as_formula(*u);
            args.clear();
            tmp.clear();
            match view_u {
                View::Atom(_) => return,
                View::Not(_) => return,
                View::Eq(..) => return,
                View::Bool(true) => {
                    cs.push(&[TheoryLit::new_b(*u, true)]) // clause [true]
                },
                View::Bool(false) => {
                    // TODO: is this needed? `u` maps to `not true` anyway?
                    cs.push(&[TheoryLit::new_b(*u, false)]) // clause [¬false]
                },
                View::And(args2) => {
                    args.extend_from_slice(args2);
                    drop(view_u);
                    let mut lmb = LitMapB{lit_map, m};
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
                },
                View::Or(args2) => {
                    args.extend_from_slice(args2);
                    drop(view_u);
                    let mut lmb = LitMapB{lit_map, m};
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
                },
                View::Imply(args2) => {
                    // same as `or`, but all literals but the last are negated
                    args.extend_from_slice(args2);
                    drop(view_u);
                    let mut lmb = LitMapB{lit_map, m};
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
                },
                View::Distinct(args) if args.len() <= 2 => (),
                View::Distinct(args2) => {
                    // eliminate `distinct` into a conjunction of O(n^2) dis-equations
                    args.extend_from_slice(args2);
                    drop(view_u);
                    let mut lmb = LitMapB{lit_map, m};
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
                                let t = m.mk_eq(t_i, t_j);
                                TheoryLit::new_t(t, true)
                            };

                            // `distinct => args[i]!=args[j]`
                            cs.push(&[!lit_distinct, !eqn_i_j]);

                            // enrich the big conjunction
                            tmp.push(eqn_i_j);
                        }
                    }
                    cs.push(&tmp);
                },
            }
        });

        {
            // unit clause asserting that `t` is true
            let mut lmb = LitMapB{lit_map, m};
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

