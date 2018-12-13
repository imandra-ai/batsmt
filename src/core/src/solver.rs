
//! Main SMT solver

use {
    batsat::{
        self as sat,lbool,
        theory::CheckRes,
    },
    batsmt_pretty as pp,
    crate::{
        ast::{self,AST},
        lit_map::{LitMap},
        theory::{Theory,TheoryLit,TheoryClause,Actions,ActState,Trail},
        symbol::Symbol,
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

/// used to build SAT clauses efficiently
struct BClauseBuild<'a,S:Symbol,F:FnMut() -> sat::Var> {
    lits: &'a mut Vec<BLit>,
    lit_map: &'a mut LitMap<S>,
    f: F,
}

/// The theory given to the SAT solver
struct CoreTheory<S:Symbol, Th: Theory<S>> {
    m: ast::Manager<S>,
    th: Th,
    lit_map: LitMap<S>,
    acts: Actions,
    lits: Vec<BLit>,
    th_trail: Vec<(AST,bool,BLit)>, // temporary for trail slices
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
        pub fn new(m: &ast::Manager<S>, b: Builtins, th: Th) -> Self {
            let lit_map = LitMap::new(m, b.into());
            let c = CoreTheory {
                m: m.clone(),
                lit_map: lit_map.clone(),
                lits: Vec::new(),
                th,
                acts: Actions::new(),
                th_trail: Vec::new(),
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
                .map(|&lit| {
                    let lit = s0.get_or_create_lit(lit);
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
            trace!("assumptions: {:?}", assumptions);
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
        #[inline(always)]
        fn map_lit(&self, lit: BLit) -> Option<(AST, bool)> {
            self.lit_map.map_lit(lit)
        }
    }

    // `CoreTheory` is a SAT theory
    impl<S:Symbol, Th: Theory<S>> batsat::Theory for CoreTheory<S,Th> {
        fn create_level(&mut self) { self.th.push_level() }

        fn pop_levels(&mut self, n: usize) { self.th.pop_levels(n) }

        // main check
        fn final_check<A>(&mut self, a: &mut A) -> CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            trace!("solver.final-check ({} elts in trail)", a.model().len());

            // obtain theory literals from `a`
            self.th_trail.clear();
            for &lit in a.model().iter() {
                if let Some((t,sign)) = self.map_lit(lit) {
                    self.th_trail.push((t,sign,lit));
                }
            }

            if self.th_trail.len() == 0 {
                // nothing to do
                debug!("no theory lits in the model, return Done");
                return CheckRes::Done; // trivial
            }

            self.acts.clear(); // reset
            self.th.final_check(&mut self.acts, &Trail(&self.th_trail));

            // used to convert theory clauses into boolean clauses
            match self.acts.state() {
                ActState::Props(cs) => {
                    for c in cs.iter() {
                        trace!("add theory lemma {}", pp::display(self.m.pp(c)));
                        let mut cbuild =
                            BClauseBuild::new(&mut self.lits, &mut self.lit_map,
                                              || { a.mk_new_lit().var() });
                        cbuild.convert_th_clause(c);
                        a.add_theory_lemma(&mut self.lits);
                    }
                    trace!("check: done");
                    CheckRes::Done
                },
                ActState::Conflict(c) => {
                    trace!("build conflict clause {}", pp::display(self.m.pp(c)));
                    let mut cbuild =
                        BClauseBuild::new(&mut self.lits, &mut self.lit_map,
                                          || { a.mk_new_lit().var() });
                    cbuild.convert_th_clause(c);
                    drop(cbuild); // to borrow `a`
                    let confl = a.mk_conflict(&mut self.lits);
                    trace!("check: conflict");
                    CheckRes::Conflict(confl)
                }
            }
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

    impl<'a, S:Symbol, F:FnMut()->sat::Var> BClauseBuild<'a,S,F> {
        fn new(lits: &'a mut Vec<BLit>, lit_map: &'a mut LitMap<S>, f: F) -> Self {
            Self { lits, lit_map, f }
        }

        /// Convert a theory literal into a boolean literal
        fn convert_th_lit(&mut self, lit: TheoryLit) -> BLit {
            let f = &mut self.f;
            match lit {
                TheoryLit::B(l) => l,
                TheoryLit::BLazy(t,sign) => {
                    let bidir = false;
                    self.lit_map.get_term_or_else(t, sign, bidir, || f())
                },
                TheoryLit::T(t,sign) => {
                    let bidir = true; // theory lit
                    self.lit_map.get_term_or_else(t, sign, bidir, || f())
                },
            }
        }

        /// Convert the given theory clause into an array of boolean literals.
        ///
        /// The result is stored in `lits`
        fn convert_th_clause(&mut self, c: &[TheoryLit]) {
            self.lits.clear();
            for &lit in c.iter() {
                let lit = self.convert_th_lit(lit);
                self.lits.push(lit);
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

