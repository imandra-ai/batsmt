
//! Main SMT solver

use {
    std::fmt,
    batsat::{
        self as sat,lbool,
        theory::CheckRes,
    },
    batsmt_pretty as pp,
    batsmt_theory::{
        Theory, TheoryLit,
        TheoryClauseRef, Actions, ActState, Trail,
    },
    batsmt_core::{
        ast::{self,AST},
        symbol::Symbol,
        backtrack,
    },
    crate::{
        lit_map::{LitMap},
    },
};

///A boolean literal
pub use crate::blit::BLit;

#[derive(Copy,Clone,Debug)]
pub struct Builtins {
    pub bool_: AST, // the boolean sort
    pub true_: AST, // term for `true`
    pub false_: AST, // term for `false`
    pub not_: AST,
}

/// used to build SAT clauses efficiently
struct BClauseBuild<'a,S:Symbol,F:FnMut() -> sat::Var> {
    lits: &'a mut Vec<sat::Lit>,
    lit_map: &'a mut LitMap<S>,
    f: F,
}

/// The theory given to the SAT solver
struct CoreTheory<S:Symbol, Th: Theory<S,BLit>> {
    m: ast::Manager<S>,
    th: Th,
    lit_map: LitMap<S>,
    acts: Actions<BLit>,
    lits: Vec<sat::Lit>,
    trail_offset: backtrack::Ref<usize>, // current offset in the trail for the theory
    th_trail: Vec<(AST,bool,BLit)>, // temporary for trail slices
}

/// A SMT solver.
///
/// It is parametrized over the concrete type of symbols, and
/// a theory to interpret boolean terms.
pub struct Solver<S:Symbol, Th: Theory<S, BLit>> {
    s0: Solver0<S,Th>,
    m: ast::Manager<S>,
    lits: Vec<sat::Lit>, // temporary for clause
}

struct Solver0<S:Symbol, Th: Theory<S, BLit>> {
    sat: batsat::Solver<solver::Cb, CoreTheory<S, Th>>,
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

    // public API
    impl<S:Symbol, Th: Theory<S, BLit>> Solver<S,Th> {
        /// New Solver, using the given theory `th` and AST manager
        pub fn new(m: &ast::Manager<S>, b: Builtins, th: Th) -> Self {
            let lit_map = LitMap::new(m, b.into());
            let c = CoreTheory {
                m: m.clone(),
                lit_map: lit_map.clone(),
                lits: Vec::new(),
                th,
                acts: Actions::new(),
                trail_offset: backtrack::Ref::new(0),
                th_trail: Vec::new(),
            };
            let cb = Cb::new();
            let mut opts = batsat::SolverOpts::default();
            opts.luby_restart = false;
            opts.restart_first = 1000;
            opts.restart_inc = 15.;
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
        pub fn add_bool_clause_reuse(&mut self, c: &mut Vec<sat::Lit>) {
            trace!("solver.add-bool-clause {:?}", c);
            self.s0.sat.add_clause_reuse(c);
        }

        /// Add a clause made from signed terms
        pub fn add_clause(&mut self, c: TheoryClauseRef<BLit>) {
            trace!("solver.add-clause\n{}", self.m.pp(c));
            // use `self.lits` as temporary storage
            self.lits.clear();
            let s0 = &mut self.s0;
            self.lits.extend(
                c.iter()
                .map(|lit| {
                    let lit = s0.get_or_create_lit(lit);
                    lit.0
                }));
            self.s0.sat.add_clause_reuse(&mut self.lits);
        }

        // TODO: find how to avoid duplicating work if called in a (refinement) loop
        // first, add theory literals to the theory
        fn add_initial_literals(&mut self) {
            debug!("solver.theory.add-lits");
            let th = &mut self.s0.sat.theory_mut();
            for (t,blit) in self.s0.lit_map.get().iter_theory_lits() {
                th.th.add_literal(t,blit);
            }
            let acts = &mut th.acts;
            th.th.final_check(acts, &Trail::empty());
            assert!(acts.is_sat()); // no conflict by just addings lits
        }

        /// Solve the set of constraints added with `add_clause` until now
        pub fn solve_with(&mut self, assumptions: &[sat::Lit]) -> Res {
            info!("solver.sat.solve ({} assumptions)", assumptions.len());

            self.add_initial_literals();

            trace!("assumptions: {:?}", assumptions);
            let sat = &mut self.s0.sat;
            let r = sat.solve_limited(assumptions);
            info!("solver.sat.stats: conflicts {}, decisions {}, propagations {}, {}",
                  sat.num_conflicts(), sat.num_decisions(),
                  sat.num_propagations(), sat.cb().stats());
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

    impl<S:Symbol, Th: Theory<S, BLit>> CoreTheory<S, Th> {
        #[inline(always)]
        fn map_lit(&self, lit: BLit) -> Option<(AST, bool)> {
            self.lit_map.map_lit(lit)
        }

        // internal checking
        fn check<A>(&mut self, partial: bool, a: &mut A) -> CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            // no need to parse the trail or do anything, if the theory doesn't support partial
            // checks
            if partial && ! Th::has_partial_check() {
                return CheckRes::Done;
            }

            // obtain theory literals from `a`.
            // do we use the full model, or just what's not been examined last?
            let model = {
                if partial {
                    let offset = *self.trail_offset.get();
                    let tr = a.model();
                    &tr[offset..]
                } else if Th::has_partial_check() {
                    &[] // already got the whole trail
                } else {
                    a.model()
                }
            };

            self.th_trail.clear();
            for &lit in model.iter() {
                let lit = BLit::new(lit);
                if let Some((t,sign)) = self.map_lit(lit) {
                    self.th_trail.push((t,sign,lit));
                }
            }

            trace!("solver.{}-check ({} level(s), \
                {} elt(s) in trail, among which {} from theory)",
                if partial {"partial"} else {"final"},
                self.th.n_levels(), a.model().len(), self.th_trail.len());

            if self.th_trail.len() == 0 {
                // nothing to do
                trace!("no theory lits in the model, return Done");
                return CheckRes::Done; // trivial
            }

            self.acts.clear(); // reset
            if partial {
                self.th.partial_check(&mut self.acts, &Trail::from_slice(&self.th_trail));

                // update which section of the trail we've checked so far, so
                // that the theory won't see this section again in `final_check`
                *self.trail_offset = a.model().len();
            } else {
                self.th.final_check(&mut self.acts, &Trail::from_slice(&self.th_trail));
            }

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
                ActState::Conflict{c, costly} => {
                    trace!("build conflict clause {} (costly {})", pp::display(self.m.pp(c)), costly);
                    let mut cbuild =
                        BClauseBuild::new(&mut self.lits, &mut self.lit_map,
                                          || { a.mk_new_lit().var() });
                    cbuild.convert_th_clause(c);
                    drop(cbuild); // to borrow `a`
                    let confl = a.mk_conflict(&mut self.lits, costly);
                    trace!("check: conflict");
                    CheckRes::Conflict(confl)
                }
            }
        }
    }

    // `CoreTheory` is a SAT theory
    impl<S:Symbol, Th: Theory<S, BLit>> batsat::Theory for CoreTheory<S,Th> {
        fn create_level(&mut self) {
            self.trail_offset.push_level();
            self.th.push_level();
        }
        fn pop_levels(&mut self, n: usize) {
            self.trail_offset.pop_levels(n);
            self.th.pop_levels(n);
        }
        fn n_levels(&self) -> usize {
            let n = self.th.n_levels();
            debug_assert_eq!(n, self.trail_offset.n_levels());
            n
        }

        // main check
        fn final_check<A>(&mut self, a: &mut A) -> CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            self.check(false, a)
        }

        fn partial_check<A>(&mut self, a: &mut A) -> CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            self.check(true, a)
        }
    }

    impl<S:Symbol, Th: Theory<S, BLit>> Solver0<S,Th> {
        // find or make a literal for `t`
        fn get_or_create_lit(&mut self, l: TheoryLit<BLit>) -> BLit {
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
        fn new(lits: &'a mut Vec<sat::Lit>, lit_map: &'a mut LitMap<S>, f: F) -> Self {
            Self { lits, lit_map, f }
        }

        /// Convert a theory literal into a boolean literal
        fn convert_th_lit(&mut self, lit: TheoryLit<BLit>) -> BLit {
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
        fn convert_th_clause(&mut self, c: TheoryClauseRef<BLit>) {
            self.lits.clear();
            for lit in c.iter() {
                let lit = self.convert_th_lit(lit);
                self.lits.push(lit.0);
            }
        }
    }

    /// Used for callbacks
    pub(super) struct Cb {
        n_restarts: u32,
        n_gc_calls: u32,
    }

    impl Cb {
        fn new() -> Self {
            Cb {
                n_restarts: 0, n_gc_calls: 0,
            }
        }

        fn stats<'a>(&'a self) -> impl fmt::Display+'a { self }
    }

    impl fmt::Display for Cb {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "restarts: {}, gc.calls: {}",
                   self.n_restarts, self.n_gc_calls)
        }
    }

    impl batsat::Callbacks for Cb {
        fn on_restart(&mut self) { self.n_restarts += 1 }
        fn on_gc(&mut self, _: usize, _: usize) { self.n_gc_calls += 1; }
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

