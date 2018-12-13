
//! Main SMT solver

use batsat::{self,lbool};
use {
    crate::{
        ast::{self,AST},
        lit_map::{LitMap},
        theory::{Theory,TheoryLit,TheoryClause,Actions}, symbol::Symbol,
    },
};

/// A boolean literal
pub use batsat::Lit as BLit;

/// A boolean variable
pub use batsat::Var as BVar;

#[derive(Copy,Clone,Debug)]
pub struct Builtins {
    pub bool_: AST, // the boolean sort
    pub true_: AST, // term for `true`
    pub false_: AST, // term for `false`
    pub not_: AST,
}

/// The theory given to the SAT solver
struct CoreTheory<S:Symbol, Th: Theory<S>> {
    m: ast::Manager<S>,
    th: Th,
    lit_map: LitMap<S>,
    acts: Actions,
}

/// A SMT solver.
///
/// It is parametrized over the concrete type of symbols, and
/// a theory to interpret boolean terms.
pub struct Solver<S:Symbol, Th: Theory<S>> {
    s0: Solver0<S,Th>,
    m: ast::Manager<S>,
    lits: Vec<BLit>, // temporary for clause
}

struct Solver0<S:Symbol, Th: Theory<S>> {
    sat: batsat::Solver<batsat::BasicCallbacks, CoreTheory<S, Th>>,
    lit_map: LitMap<S>,
}

/// Result of a call to `solve`
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Res {
    SAT,
    UNSAT,
}

mod solver {
    use super::*;
    use batsat::SolverInterface;

    impl<S:Symbol, Th: Theory<S>> Solver<S,Th> {
        /// New Solver, using the given theory `th` and AST manager
        pub fn new(m: &ast::Manager<S>, b: Builtins, th: Th) -> Self
        {
            let lit_map = LitMap::new(m, b.into());
            let c = CoreTheory {
                m: m.clone(),
                lit_map: lit_map.clone(),
                th,
                acts: Actions::new(),
            };
            let opts = batsat::SolverOpts::default();
            let cb = batsat::BasicCallbacks::new();
            // create SAT solver
            let sat = batsat::Solver::new_with(opts, cb, c);
            let mut s = Solver {
                s0: Solver0 { sat, lit_map, },
                m: m.clone(),
                lits: Vec::new(),
            };
            s.init_logic();
            s
        }

        // initial axioms,etc.
        fn init_logic(&mut self) {
            trace!("solver.init-logic")
        }

        /// Access literal map of this solver
        pub fn lit_map(&self) -> & LitMap<S> { & self.s0.lit_map }

        /// Add a boolean clause
        pub fn add_bool_clause_reuse(&mut self, c: &mut Vec<BLit>) {
            trace!("solver.add-bool-clause {:?}", c);
            self.s0.sat.add_clause_reuse(c);
        }

        /// Add a clause made from signed terms
        pub fn add_clause_slice(&mut self, c: &[TheoryLit]) {
            trace!("solver.add-clause\n{}", self.m.display(c));
            // use `self.lits` as temporary storage
            self.lits.clear();
            let s0 = &mut self.s0;
            self.lits.extend(
                c.iter()
                .map(|lit| {
                    let lit = s0.get_or_create_lit(*lit);
                    lit
                }));
            self.s0.sat.add_clause_reuse(&mut self.lits);
        }

        /// Add a clause made from signed terms
        pub fn add_clause(&mut self, c: &TheoryClause) {
            self.add_clause_slice(& *c)
        }

        /// Solve the set of constraints added with `add_clause` until now
        pub fn solve_with(&mut self, assumptions: &[BLit]) -> Res {
            info!("solver.sat.solve ({} assumptions)", assumptions.len());
            let r = self.s0.sat.solve_limited(assumptions);
            // convert result
            if r == lbool::TRUE {
                Res::SAT
            } else {
                assert_eq!(r, lbool::FALSE);
                Res::UNSAT
            }
        }

        /// Solve without assumptions
        pub fn solve(&mut self) -> Res {
            self.solve_with(&[])
        }
    }

    impl<S:Symbol, Th: Theory<S>> CoreTheory<S, Th> {
        fn map_term(&self, t: AST, sign: bool) -> BLit {
            self.lit_map.get_term(t,sign).expect("term doesn't map to a literal")
        }

        fn map_lit(&self, lit: BLit) -> (AST, bool) {
            self.lit_map.map_lit(lit)
        }
    }

    // `CoreTheory` is a SAT theory
    impl<S:Symbol, Th: Theory<S>> batsat::Theory for CoreTheory<S,Th> {
        fn create_level(&mut self) { self.th.push_level() }

        fn pop_levels(&mut self, n: usize) { self.th.pop_levels(n) }

        // main check
        fn final_check<A>(&mut self, a: &mut A)
            -> batsat::theory::CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            trace!("solver.final-check ({} elts in trail)", a.model().len());
            unimplemented!() // TODO: filter_map into theory lits, clear actions, call theory, process action
        }
    }

    impl<S:Symbol, Th: Theory<S>> Solver0<S,Th> {
        // find or make a literal for `t`
        fn get_or_create_lit(&mut self, l: TheoryLit) -> BLit {
            match l {
                TheoryLit::B(l) => l,
                TheoryLit::BLazy(t,sign) => {
                    let sat = &mut self.sat;
                    let bidir = false;
                    self.lit_map.get_term_or_else(t, sign, bidir,
                                                  || { sat.new_var_default() })
                },
                TheoryLit::T(t,sign) => {
                    let sat = &mut self.sat;
                    let bidir = true; // theory lit
                    self.lit_map.get_term_or_else(t, sign, bidir,
                                                  || { sat.new_var_default() })
                },
            }
        }
    }
}

mod builtins {
    use crate::lit_map::Builtins as BoolBuiltins;
    use super::*;

    impl Into<BoolBuiltins> for Builtins {
        fn into(self) -> BoolBuiltins {
            let Builtins {true_, false_, bool_, not_} = self;
            BoolBuiltins { true_, false_, bool_, not_}
        }
    }
}

