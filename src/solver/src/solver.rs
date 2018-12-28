
//! Main SMT solver

use {
    std::{fmt, marker::PhantomData},
    batsat::{
        self as sat,lbool,
        theory::CheckRes,
    },
    batsmt_pretty::{self as pp, Pretty1},
    batsmt_theory::{ self as theory,
        Ctx, Theory, TheoryLit, TheoryClauseRef, Trail,
        LitMap,
    },
    batsmt_core::{
        backtrack, ast_u32::{AST, },
    },
    crate::{
        lit_map::{SatLitMap},
    },
};

pub use {
    batsmt_theory::LitMapBuiltins as Builtins,
    crate::blit::BLit,
};

/// used to build SAT clauses efficiently
struct BClauseBuild<'a,F:FnMut() -> sat::Var> {
    lits: &'a mut Vec<sat::Lit>,
    lit_map: &'a mut SatLitMap,
    f: F,
}

/// The theory given to the SAT solver
struct CoreTheory<C: Ctx<B=BLit>, Th: Theory<C>> {
    th: Th,
    lit_map: SatLitMap,
    acts: theory::Actions<C>,
    lits: Vec<sat::Lit>,
    trail_offset: backtrack::Ref<usize>, // current offset in the trail for the theory
    th_trail: Vec<(AST,bool,BLit)>, // temporary for trail slices
}

/// Temporary bundle of theory + context, to be passed to the SAT solver.
struct TheoryTmp<'a, C: Ctx<B=BLit>, Th: Theory<C>>(&'a mut CoreTheory<C,Th>, &'a mut C);

/// A SMT solver.
///
/// It is parametrized over the concrete type of symbols, and
/// a theory to interpret boolean terms.
pub struct Solver<C: Ctx<B=BLit>, Th: Theory<C>> {
    s0: Solver0<C,Th>,
    lits: Vec<sat::Lit>, // temporary for clause
}

struct Solver0<C: Ctx<B=BLit>, Th: Theory<C>> {
    c: CoreTheory<C, Th>,
    sat: batsat::Solver<solver::Cb>,
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
    impl<C,Th> Solver<C,Th>
        where C: Ctx<B=BLit>, Th: Theory<C>
    {
        /// New Solver, using the given theory `th` and AST manager.
        pub fn new(b: Builtins, th: Th) -> Self {
            let lit_map = SatLitMap::new(b.clone());
            let c = CoreTheory {
                lits: Vec::new(),
                th,
                lit_map, 
                acts: theory::Actions::new(),
                trail_offset: backtrack::Ref::new(0),
                th_trail: Vec::new(),
            };
            let cb = Cb::new();
            let mut opts = batsat::SolverOpts::default();
            opts.luby_restart = false;
            opts.restart_first = 1000;
            opts.restart_inc = 15.;
            // create SAT solver
            let sat = batsat::Solver::new_with(opts, cb);
            let mut s = Solver {
                s0: Solver0 { sat, c, },
                lits: Vec::new(),
            };
            s.init_logic();
            s
        }

        // initial axioms,etc.
        fn init_logic(&mut self) {
            trace!("solver.init-logic")
        }

        /// Access literal map of this solver.
        #[inline(always)]
        pub fn lit_map(&self) -> &SatLitMap { & self.s0.c.lit_map }

        /// Access literal map of this solver.
        #[inline(always)]
        pub fn lit_map_mut(&mut self) -> &mut SatLitMap { &mut self.s0.c.lit_map }

        /// Add a boolean clause.
        pub fn add_bool_clause_reuse(&mut self, c: &mut Vec<sat::Lit>) {
            trace!("solver.add-bool-clause {:?}", c);
            self.s0.sat.add_clause_reuse(c);
        }

        /// Add a clause made from signed terms.
        pub fn add_clause(&mut self, m: &C, c: TheoryClauseRef<C>) {
            trace!("solver.add-clause\n{}", c.pp(m));
            // use `self.lits` as temporary storage
            self.lits.clear();
            let s0 = &mut self.s0;
            self.lits.extend(
                c.iter()
                .map(|lit| {
                    let lit = s0.get_or_create_lit(m, lit);
                    lit.0
                }));
            self.s0.sat.add_clause_reuse(&mut self.lits);
        }

        // TODO: find how to avoid duplicating work if called in a (refinement) loop
        // first, add theory literals to the theory
        fn add_initial_literals(&mut self, m: &mut C) {
            debug!("solver.theory.add-lits");
            let core = &mut self.s0.c;
            for (t,blit) in core.lit_map.iter_theory_lits() {
                core.th.add_literal(m,t,blit);
            }
            let acts = &mut core.acts;
            core.th.final_check(m, acts, &Trail::empty());
            assert!(acts.is_sat()); // no conflict by just addings lits
        }

        /// Solve the set of constraints added with `add_clause` until now
        pub fn solve_with(&mut self, m: &mut C, assumptions: &[sat::Lit]) -> Res {
            info!("solver.sat.solve ({} assumptions)", assumptions.len());

            self.add_initial_literals(m);

            trace!("assumptions: {:?}", assumptions);
            let sat = &mut self.s0.sat;
            let r = {
                // temporary theory, pass it to SAT
                let mut th = TheoryTmp(&mut self.s0.c, m);
                sat.solve_limited_th(&mut th, assumptions)
            };
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
        pub fn solve(&mut self, m: &mut C) -> Res {
            self.solve_with(m, &[])
        }
    }

    impl<C,Th> CoreTheory<C, Th>
        where C: Ctx<B=BLit>, Th: Theory<C>
    {
        #[inline(always)]
        fn map_lit(&self, lit: BLit) -> Option<(AST, bool)> {
            self.lit_map.map_lit(lit)
        }

        // internal checking
        fn check<A>(&mut self, m: &mut C, partial: bool, a: &mut A) -> CheckRes<A::Conflict>
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
                self.th.n_levels(), model.len(), self.th_trail.len());

            if self.th_trail.len() == 0 {
                // nothing to do
                trace!("no theory lits in the model, return Done");
                return CheckRes::Done; // trivial
            }

            self.acts.clear(); // reset
            if partial {
                self.th.partial_check(m, &mut self.acts, &Trail::from_slice(&self.th_trail));

                // update which section of the trail we've checked so far, so
                // that the theory won't see this section again in `final_check`
                *self.trail_offset = a.model().len();
            } else {
                self.th.final_check(m, &mut self.acts, &Trail::from_slice(&self.th_trail));
            }

            // used to convert theory clauses into boolean clauses
            match self.acts.state() {
                theory::ActState::Props {lemmas, props} => {
                    for &p in props.iter() {
                        trace!("propagate literal {:?}", p);
                        a.propagate(p.0)
                    }
                    for c in lemmas.iter() {
                        trace!("add theory lemma {}", pp::display(&c.pp(m)));
                        let mut cbuild =
                            BClauseBuild::new(&mut self.lits, &mut self.lit_map,
                                              || { a.mk_new_lit().var() });
                        cbuild.convert_th_clause(m, c);
                        a.add_theory_lemma(&mut self.lits);
                    }
                    trace!("check: done");
                    CheckRes::Done
                },
                theory::ActState::Conflict{c, costly} => {
                    trace!("build conflict clause {} (costly {})", pp::display(c.pp(m)), costly);
                    let mut cbuild =
                        BClauseBuild::new(&mut self.lits, &mut self.lit_map,
                                          || { a.mk_new_lit().var() });
                    cbuild.convert_th_clause(m, c);
                    drop(cbuild); // to borrow `a`
                    let confl = a.mk_conflict(&mut self.lits, costly);
                    trace!("check: conflict");
                    CheckRes::Conflict(confl)
                }
            }
        }
    }

    // `CoreTheory` is a SAT theory
    impl<'a, C, Th> batsat::Theory for TheoryTmp<'a,C,Th>
        where C: Ctx<B=BLit>, Th: Theory<C>
    {
        fn create_level(&mut self) {
            self.0.trail_offset.push_level();
            self.0.th.push_level(self.1);
        }
        fn pop_levels(&mut self, n: usize) {
            self.0.trail_offset.pop_levels(n);
            self.0.th.pop_levels(self.1, n);
        }
        fn n_levels(&self) -> usize {
            let n = self.0.th.n_levels();
            debug_assert_eq!(n, self.0.trail_offset.n_levels());
            n
        }

        // main check
        fn final_check<A>(&mut self, a: &mut A) -> CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            self.0.check(self.1, false, a)
        }

        fn partial_check<A>(&mut self, a: &mut A) -> CheckRes<A::Conflict>
            where A: batsat::theory::TheoryArgument
        {
            self.0.check(self.1, true, a)
        }

        fn explain_propagation(&mut self, p: sat::Lit) -> &[sat::Lit] {
            // copy explanation from theory
            self.0.lits.clear();
            let e = self.0.th.explain_propagation(self.1, BLit(p)).iter().map(|l| l.0);
            self.0.lits.extend(e);
            &self.0.lits
        }
    }

    impl<C, Th> Solver0<C,Th>
        where C: Ctx<B=BLit>, Th: Theory<C>
    {
        // find or make a literal for `t`
        fn get_or_create_lit(&mut self, ctx: &C, l: TheoryLit<C>) -> BLit {
            match l {
                TheoryLit::B(l) => l,
                TheoryLit::BLazy(t,sign) => {
                    let sat = &mut self.sat;
                    let bidir = false;
                    let newlit = || {
                        BLit::from_var(sat.new_var_default(), true)
                    };
                    self.c.lit_map.get_term_or_else(ctx, &t, sign, bidir, newlit)
                },
                TheoryLit::T(t,sign) => {
                    let sat = &mut self.sat;
                    let bidir = true; // theory lit
                    let newlit = || {
                        BLit::from_var(sat.new_var_default(), true)
                    };
                    self.c.lit_map.get_term_or_else(ctx, &t, sign, bidir, newlit)
                },
            }
        }
    }

    impl<'a, F:FnMut()->sat::Var> BClauseBuild<'a,F> {
        fn new(lits: &'a mut Vec<sat::Lit>, lit_map: &'a mut SatLitMap, f: F) -> Self {
            Self { lits, lit_map, f }
        }

        /// Convert a theory literal into a boolean literal
        fn convert_th_lit<C>(&mut self, ctx: &C, lit: TheoryLit<C>) -> BLit
            where C: Ctx<B=BLit>
        {
            let f = &mut self.f;
            match lit {
                TheoryLit::B(l) => l,
                TheoryLit::BLazy(t,sign) => {
                    let bidir = false;
                    self.lit_map.get_term_or_else(ctx, &t, sign, bidir, || BLit::from_var(f(), true))
                },
                TheoryLit::T(t,sign) => {
                    let bidir = true; // theory lit
                    self.lit_map.get_term_or_else(ctx, &t, sign, bidir, || BLit::from_var(f(), true))
                },
            }
        }

        /// Convert the given theory clause into an array of boolean literals.
        ///
        /// The result is stored in `lits`
        fn convert_th_clause<C>(&mut self, m: &C, c: TheoryClauseRef<C>)
            where C: Ctx<B=BLit>
        {
            self.lits.clear();
            for lit in c.iter() {
                let lit = self.convert_th_lit(m, lit);
                self.lits.push(lit.0);
            }
        }
    }

    /// Used for callbacks in the SAT solver.
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
        #[inline(always)]
        fn on_restart(&mut self) { self.n_restarts += 1 }
        #[inline(always)]
        fn on_gc(&mut self, _: usize, _: usize) { self.n_gc_calls += 1; }
    }
}
