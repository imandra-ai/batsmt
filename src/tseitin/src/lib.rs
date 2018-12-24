
//! Tseitin Transformation

use {
    batsmt_core::{
        ast::{self,AST,View,iter_dag::State as AstIter},
        Symbol,
    },
    batsmt_theory::{TheoryLit,TheoryClauseSet,TheoryClauseRef},
    batsmt_solver::{
        lit_map::LitMap, BLit,
    },
};

type M<S> = ast::Manager<S>;

/// Tseitin transformation
#[derive(Clone)]
pub struct Tseitin<S:Symbol> {
    m: M<S>, // manager
    b: Builtins,
    iter: AstIter<S>, // to traverse subterms
    tmp: Vec<TheoryLit<BLit>>, // temp clause
    tmp2: Vec<TheoryLit<BLit>>, // temp clause
    lit_map: LitMap<S>,
    cs: TheoryClauseSet<BLit>, // clauses
}

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

// temporary structure
struct LitMapB<'a, S:Symbol> {
    m: M<S>,
    lit_map: &'a LitMap<S>,
    b: Builtins,
}

impl<'a, S:Symbol> LitMapB<'a,S> {
    /// Map `t,sign` to either a theory literal, or a lazy pure boolean literal
    fn term_to_lit(&self, t: AST) -> TheoryLit<BLit> {
        let (t,sign) = self.lit_map.unfold_not(t, true);
        let b = &self.b;
        let mut mr = self.m.get_mut();
        let view_t = mr.view(t);
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
                        drop(view_t); // to get `mr` again
                        let eqn = mr.mk_app(b.eq, &[t0, t1]);
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

impl<S:Symbol> Tseitin<S> {
    /// Create a new Tseitin transformation
    pub fn new(m: &M<S>, lit_map: &LitMap<S>, b: Builtins) -> Self {
        Self {
            b, m: m.clone(),
            lit_map: lit_map.clone(),
            tmp: Vec::new(),
            tmp2: Vec::new(),
            iter: AstIter::new(&m),
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

    /// `tseitin.clauses(t)` turns the boolean term `t` into a set of clauses.
    ///
    /// The clauses define boolean connectives occurring inside `t`.
    /// ## params
    /// - `t` is the formula to normalize
    pub fn clauses(&mut self, t: AST) -> impl Iterator<Item=TheoryClauseRef<BLit>> {
        self.cs.clear();

        let Tseitin {
            b, ref mut cs, m, lit_map,
            ref mut tmp, ref mut tmp2, ..} = self;
        let lmb = LitMapB{lit_map, b: b.clone(), m: m.clone()};

        {
            // traverse `t` as a DAG
            self.iter.iter(t, |m, u| {
                // `u` is a subterm that has never been processed.
                let mut mr = m.get_mut();
                let view_u = mr.view(u);
                match view_u {
                    View::App {f, args} if f == b.not_ => {
                        debug_assert_eq!(1, args.len());
                        () // nothing to do here
                    },
                    View::App {f, args} if f == b.and_ => {
                        // obtain literals for subterms of the `and` into `tmp`
                        tmp.clear();
                        for &t in args.iter() {
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
                            for &sub in tmp.iter() { tmp2.push(!sub) }
                            tmp2.push(lit_and);
                            cs.push(&tmp2);
                        }
                    },
                    View::App {f, args} if f == b.or_ => {
                        // obtain literals for subterms of the `or` into `tmp`
                        tmp.clear();
                        for &t in args.iter() {
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
                    View::App {f, args} if f == b.imply_ => {
                        // same as `or`, but all literals but the last are negated
                        assert!(args.len() >= 1);
                        tmp.clear();
                        {
                            let t_last = args[args.len()-1];
                            tmp.push(lmb.term_to_lit(t_last));
                        }
                        for &t in args[.. args.len()-1].iter() {
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
                    _ if u == b.true_ => {
                        cs.push(&[TheoryLit::new_b(u, true)]) // clause [true]
                    },
                    _ if u == b.false_ => {
                        // TODO: is this needed? `u` maps to `not true` anyway?
                        cs.push(&[TheoryLit::new_b(u, false)]) // clause [¬false]
                    },
                    View::App {f, args} if f == b.distinct && args.len() <= 2 => {
                        () // nop, encoded as equation
                    },
                    View::App {f, args} if f == b.distinct => {
                        let args: Vec<AST> = args.into();
                        drop(view_u); // access `mr` again

                        // eliminate `distinct` into a conjunction of O(n^2) dis-equations
                        let lit_distinct = lmb.term_to_lit(u);

                        // `∧i args[i]!=args[j] => distinct`
                        tmp.clear();
                        tmp.push(lit_distinct);

                        for i in 0 .. args.len()-1 {
                            let t_i = args[i];
                            for j in i+1 .. args.len() {
                                let t_j = args[j];
                                let eqn_i_j = {
                                    let t = mr.mk_app(b.eq, &[t_i, t_j]);
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
                    _ => (),
                };
            });
        }

        {
            // unit clause asserting that `t` is true
            let top_lit = lmb.term_to_lit(t);
            self.cs.push(&[top_lit]);
        }

        self.cs.iter()
    }

}

