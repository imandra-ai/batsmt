
//! Main SMT solver

use {
    std::{fmt, marker::PhantomData, },
    batsat as sat,
    batsmt_theory::{ self as theory,
        Ctx, Theory, TheoryLit, TheoryClauseRef, Trail, LitMap},
    batsmt_core::{ backtrack, ast_u32::{AST, }, },
    crate::{ lit_map::{SatLitMap}, },
};

pub use {
    batsmt_theory::LitMapBuiltins as Builtins,
    batsat::lbool,
    crate::blit::BLit,
};

/// The theory given to the SAT solver
struct CoreTheory<C: Ctx<B=BLit>, Th: Theory<C>> {
    th: Th,
    lit_map: SatLitMap,
    lits: Vec<sat::Lit>,
    trail_offset: backtrack::Ref<usize>, // current offset in the trail for the theory
    th_trail: Vec<(AST,bool,BLit)>, // temporary for trail slices
    th_stats: theory::Stats,
    _m: PhantomData<C>,
}

/// Temporary bundle of theory + context, to be passed to the SAT solver.
struct TheoryTmp<'a, C: Ctx<B=BLit>, Th: Theory<C>>(&'a mut CoreTheory<C,Th>, &'a mut C);

/// Temporary structure passed to the theory.
struct TmpAct<'a, A: sat::TheoryArgument> {
    ok: bool,
    stats: &'a mut theory::Stats,
    acts: &'a mut A,
    lits: &'a mut Vec<sat::Lit>,
    lit_map: &'a mut SatLitMap,
}

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

/// Map theory literals into boolean literals.
fn get_or_create_lit_<C, F>(
    ctx: &C,
    lit_map: &mut SatLitMap,
    l: TheoryLit<C>,
    f: F
) -> BLit
    where C: Ctx<B=BLit>, F: FnOnce() -> BLit
{
    match l {
        TheoryLit::B(l) => l,
        TheoryLit::BLazy(t,sign) => {
            let bidir = false;
            lit_map.get_term_or_else(ctx, &t, sign, bidir, f)
        },
        TheoryLit::T(t,sign) => {
            let bidir = true; // theory lit
            lit_map.get_term_or_else(ctx, &t, sign, bidir, f)
        },
    }
}

mod solver {
    use {
        super::*, batsat::SolverInterface,
        batsmt_pretty::{Pretty1},
        batsmt_theory::LitMap,
    };

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
                _m: PhantomData,
                th_stats: theory::Stats::new(),
                lit_map,
                trail_offset: backtrack::Ref::new(0),
                th_trail: Vec::new(),
            };
            let cb = Cb::new();
            let mut opts = batsat::SolverOpts::default();
            opts.luby_restart = false;
            opts.restart_first = 1000;
            opts.restart_inc = 15.;
            opts.min_learnts_lim = 1_200; // min number of learnt clauses
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

        /// Access statistics.
        pub fn th_stats(&self) -> &theory::Stats { &self.s0.c.th_stats }

        /// Access literal map of this solver.
        #[inline(always)]
        pub fn lit_map(&self) -> &SatLitMap { & self.s0.c.lit_map }

        /// Access literal map of this solver.
        #[inline(always)]
        pub fn lit_map_mut(&mut self) -> &mut SatLitMap { &mut self.s0.c.lit_map }

        /// Enable/disable theory propagation(s).
        pub fn enable_th_propagation(&mut self, b: bool) {
            self.s0.c.th.enable_propagation(b)
        }

        /// Add a boolean clause.
        #[inline]
        pub fn add_bool_clause_reuse(&mut self, c: &mut Vec<sat::Lit>) {
            trace!("solver.add-bool-clause {:?}", c);
            self.s0.sat.add_clause_reuse(c);
        }

        /// Allocate new boolean variable with the given default polarity.
        #[inline]
        pub fn new_bool_lit_with(&mut self, default: bool) -> sat::Lit {
            let pol = if default { lbool::TRUE } else { lbool::FALSE };
            sat::Lit::new(self.s0.sat.new_var(pol, true), true)
        }

        /// Allocate new boolean variable with default polarity `false`.
        #[inline]
        pub fn new_bool_lit(&mut self) -> sat::Lit {
            self.new_bool_lit_with(false)
        }

        /// Get or allocate new boolean variable with default polarity `false`, mapped to given term.
        pub fn new_term_lit(&mut self, ctx: &mut C, t: AST) -> BLit {
            let Solver0{sat, c, ..} = &mut self.s0;
            let lm = &mut c.lit_map;

            let f = || {
                BLit::from_var(sat.new_var_default(), true)
            };

            let bidir = true; // theory lit
            lm.get_term_or_else(ctx, &t, true, bidir, f)
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

        // add new theory literals to the theory.
        fn add_initial_literals(&mut self, m: &mut C) {
            debug!("solver.theory.add-lits");
            let core = &mut self.s0.c;
            for (t,blit) in core.lit_map.drain_new_theory_lits() {
                core.th.add_literal(m,t,blit);
            }
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
            info!("{}, sat.conflicts {}, sat.decisions {}, sat.propagations {}, {}",
                  self.s0.c.th_stats,
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

        /* TODO
        pub fn get_model(&self) -> &[(BLit, lbool)] {
            let mut v = vec!();
            for (i, v) in self.s0.sat.get_model().iter().enumerate() {
                let lit = BLit::from_var(sat::Var::from_index(i), true);
                v.push((lit, v));
            }
            v
        }
        */

        /// Unsat core
        pub fn get_unsat_core(&mut self) -> &[sat::Lit] {
            self.s0.sat.unsat_core()
        }

        /// Set of literals proved at level 0.
        #[inline]
        pub fn proved_at_lvl_0(&self) -> &[sat::Lit] {
            self.s0.sat.proved_at_lvl_0()
        }

        /// Value of the given literal at level 0 in the current trail.
        #[inline]
        pub fn value_at_lvl_0(&self, lit: BLit) -> lbool {
            self.s0.sat.value_lvl_0(lit.0)
        }

        /// Value of the given literal in the current trail/model.
        #[inline]
        pub fn value_lit(&self, lit: BLit) -> lbool {
            self.s0.sat.value_lit(lit.0)
        }

        #[inline]
        pub fn unsat_core_contains_lit(&mut self, lit: sat::Lit) -> bool {
            self.s0.sat.unsat_core_contains_lit(lit)
        }

        /// Solve without assumptions.
        pub fn solve(&mut self, m: &mut C) -> Res {
            self.solve_with(m, &[])
        }

        /// Simplify boolean clauses.
        pub fn sat_simplify(&mut self) -> Res {
            let b = self.s0.sat.simplify();
            if b { Res::SAT } else { Res::UNSAT }
        }

        pub fn n_lits(&self) -> usize { self.s0.sat.num_vars() as usize }
        pub fn n_clauses(&self) -> usize { self.s0.sat.num_clauses() as usize }
        pub fn n_conflicts(&self) -> usize { self.s0.sat.num_conflicts() as usize }
        pub fn n_props(&self) -> usize { self.s0.sat.num_propagations() as usize }
        pub fn n_decisions(&self) -> usize { self.s0.sat.num_decisions() as usize }
    }

    impl<C,Th> CoreTheory<C, Th>
        where C: Ctx<B=BLit>, Th: Theory<C>
    {
        #[inline(always)]
        fn map_lit(&self, lit: BLit) -> Option<(AST, bool)> {
            self.lit_map.map_lit(lit)
        }

        // internal checking
        fn check<A>(&mut self, m: &mut C, partial: bool, a: &mut A)
            where A: sat::theory::TheoryArgument
        {
            // no need to parse the trail or do anything, if the theory doesn't support partial
            // checks
            if partial && ! Th::has_partial_check() {
                return;
            }

            // obtain theory literals from `a`.
            // do we use the full model, or just what's not been examined last?
            let model = {
                if partial {
                    let offset = *self.trail_offset;
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
                self.trail_offset.n_levels(), model.len(), self.th_trail.len());


            // update which section of the trail we've checked so far, so
            // that the theory won't see this section again in `partial_check`
            *self.trail_offset = a.model().len();

            if partial && self.th_trail.len() == 0 {
                // nothing to do
                trace!("no theory lits in the model, nothing to do");
                return; // trivial
            }

            let CoreTheory{lits, th, lit_map, th_trail, th_stats: stats, ..} = self;
            let mut acts = TmpAct{ok: true, acts: a, lits, lit_map, stats};
            if partial {
                th.partial_check(m, &mut acts, &Trail::from_slice(&th_trail));
            } else {
                th.final_check(m, &mut acts, &Trail::from_slice(&th_trail));
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
            self.0.trail_offset.n_levels()
        }

        // main check
        fn final_check<A>(&mut self, a: &mut A)
            where A: sat::theory::TheoryArgument
        {
            self.0.check(self.1, false, a)
        }

        fn partial_check<A>(&mut self, a: &mut A)
            where A: sat::theory::TheoryArgument
        {
            self.0.check(self.1, true, a)
        }

        fn explain_propagation(&mut self, p: sat::Lit) -> &[sat::Lit] {
            // copy explanation from theory
            self.0.lits.clear();
            let blit = BLit(p);
            // map to a theory literal
            let (t, sign) = {
                let t_opt = self.0.lit_map.map_lit(blit);
                debug_assert!(t_opt.is_some(), "try to explain {:?} which is not a theory lit", p);
                t_opt.unwrap()
            };
            let e = self.0.th.explain_propagation(self.1, t, sign, blit).iter().map(|l| l.0);
            self.0.lits.extend(e);
            &self.0.lits
        }
    }

    impl<C, Th> Solver0<C,Th>
        where C: Ctx<B=BLit>, Th: Theory<C>
    {
        // find or make a literal for `t`
        #[inline]
        fn get_or_create_lit(&mut self, ctx: &C, l: TheoryLit<C>) -> BLit {
            let sat = &mut self.sat;
            let f = || {
                BLit::from_var(sat.new_var_default(), true)
            };
            get_or_create_lit_(ctx, &mut self.c.lit_map, l, f)
        }
    }

    /// Used for callbacks in the SAT solver.
    pub(super) struct Cb {
        n_restarts: u32,
        n_gc_calls: u32,
    }

    impl Cb {
        fn new() -> Self {
            Cb { n_restarts: 0, n_gc_calls: 0, }
        }

        fn stats<'a>(&'a self) -> impl fmt::Display+'a { self }
    }

    impl fmt::Display for Cb {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "sat.restarts: {}, sat.gc: {}",
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

impl<'a,C,A> theory::Actions<C> for TmpAct<'a,A>
    where C: Ctx<B=BLit>,
          A: sat::TheoryArgument
{
    #[inline(always)]
    fn propagate(&mut self, b: C::B) -> bool {
        if self.ok {
            self.stats.propagations += 1;
            self.acts.propagate(b.0)
        } else {
            false
        }
    }

    #[inline]
    fn add_lemma(&mut self, c: &[C::B]) {
        if self.ok {
            self.stats.lemmas += 1;
            self.lits.clear();
            self.lits.reserve(c.len());
            // convert `BLit -> sat::Lit`
            for BLit(a) in c.iter() { self.lits.push(*a) }
            self.acts.add_theory_lemma(&self.lits)
        }
    }

    #[inline]
    fn raise_conflict(&mut self, c: &[BLit], costly: bool) {
        if self.ok {
            trace!("theory.raise-conflict {:?} (costly: {})", c, costly);
            self.ok = false;
            self.stats.conflicts += 1;

            self.lits.clear();
            self.lits.reserve(c.len());
            // convert `BLit -> sat::Lit`
            for BLit(a) in c.iter() { self.lits.push(*a) }

            self.acts.raise_conflict(&self.lits, costly);
        }
    }

    #[inline]
    fn map_lit(&mut self, m: &C, lit: TheoryLit<C>) -> BLit {
        let TmpAct{acts,lit_map,..} = self;
        let f = || BLit(acts.mk_new_lit());
        get_or_create_lit_(m, lit_map, lit, f)
    }

    fn has_conflict(&self) -> bool { !self.ok }
}
