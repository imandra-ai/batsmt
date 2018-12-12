
//! Main SMT solver

use batsat::{self,lbool};
use {
    crate::{
        ast::{self,AST},
        lit_map::{LitMap, Builtins as BoolBuiltins},
        theory::{Theory,Actions}, symbol::Symbol,
    },
};

/// A boolean literal
pub use batsat::Lit as BLit;

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
    //sat: batsat::Solver<batsat::BasicCallbacks, CoreTheory<S, Th>>,
    sat: batsat::Solver<batsat::BasicCallbacks, CoreTheory<S, Th>>,
    lits: Vec<BLit>, // temporary for clause
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
        pub fn new(m: &ast::Manager<S>, b: BoolBuiltins, th: Th) -> Self
        {
            let c = CoreTheory {
                m: m.clone(),
                th,
                lit_map: LitMap::new(m, b),
                acts: Actions::new(),
            };
            let opts = batsat::SolverOpts::default();
            let cb = batsat::BasicCallbacks::new();
            // create SAT solver
            let sat = batsat::Solver::new_with(opts, cb, c);
            Solver {
                sat,
                lits: Vec::new(),
            }
        }

        /// Add a boolean clause
        pub fn add_bool_clause_reuse(&mut self, c: &mut Vec<BLit>) {
            debug!("solver.add-bool-clause {:?}", c);
            self.sat.add_clause_reuse(c);
        }

        /// Add a clause made from signed terms
        pub fn add_clause(&mut self, c: &[(AST, bool)]) {
            debug!("solver.add-clause {:?}", c);
            self.lits.clear();
            let sat = &mut self.sat;
            self.lits.extend(
                c.iter()
                .map(|(t,sign)| {
                    // convert terms into boolean lits
                    let lit_opt = {
                        let th = sat.theory_mut();
                        th.lit_map.map_term(*t, *sign)
                    };
                    match lit_opt {
                        Some(lit) => lit,
                        None => {
                            // allocate a new lit and add it to `lit_map`
                            let v = sat.new_var_default();
                            let lit = BLit::new(v, true);
                            let th = sat.theory_mut();
                            th.lit_map.add_term(*t, lit);
                            // put sign back
                            if *sign { lit } else {! lit}
                        }
                    }
                }));
            self.sat.add_clause_reuse(&mut self.lits);
        }

        /// Solve the set of constraints added with `add_clause` until now
        pub fn solve(&mut self, assumptions: &[BLit]) -> Res {
            info!("solver.sat.solve");
            let r = self.sat.solve_limited(assumptions);
            // convert result
            if r == lbool::TRUE {
                Res::SAT
            } else {
                assert_eq!(r, lbool::FALSE);
                Res::UNSAT
            }
        }
    }

    impl<S:Symbol, Th: Theory<S>> CoreTheory<S, Th> {
        fn map_term(&self, t: AST, sign: bool) -> BLit {
            self.lit_map.map_term(t,sign).expect("term doesn't map to a literal")
        }

        fn map_lit(&self, lit: BLit) -> (AST, bool) {
            self.lit_map.map_lit(lit)
        }
    }

    // Solver0 is a SAT theory
    impl<S:Symbol, Th: Theory<S>> batsat::Theory for CoreTheory<S,Th> {

        fn create_level(&mut self) { self.th.push_level() }

        fn pop_levels(&mut self, n: usize) { self.th.pop_levels(n) }

        // main check
        fn final_check<A>(&mut self, a: &mut A)
            -> batsat::theory::CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            unimplemented!() // TODO
        }

    }

}
