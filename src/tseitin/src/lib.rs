
//! Tseitin Transformation

use {
    batsmt_core::{
        ast::{self,AST,View,iter_dag::State as AstIter},
        Symbol,
        theory::{TheoryLit},
        lit_map::LitMap,
    },
};

// TODO: eliminate `distinct` into a n^2 conjunction of `=`

type M<S> = ast::Manager<S>;

/// Tseitin transformation
#[derive(Clone)]
pub struct Tseitin<S:Symbol> {
    m: M<S>, // manager
    b: Builtins,
    iter: AstIter<S>, // to traverse subterms
    tmp: Vec<TheoryLit>, // temp clause
    tmp2: Vec<TheoryLit>, // temp clause
    lit_map: LitMap<S>,
    cs: ClauseSet, // clauses
}

#[derive(Clone)]
struct ClauseSet {
    lits: Vec<TheoryLit>, // clause lits
    offsets: Vec<(usize,usize)>, // slices in `lits`
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
    fn term_to_lit(&self, t: AST) -> TheoryLit {
        let (t,sign) = self.lit_map.unfold_not(t, true);
        let b = &self.b;
        match self.m.get().view(t) {
            View::App {f, args: _} => {
                if f == b.true_ || f == b.false_ {
                    TheoryLit::new(t, sign)
                } else if f == b.and_ || f == b.or_ || f == b.imply_ {
                    TheoryLit::new_b(t, sign)
                } else {
                    TheoryLit::new(t, sign)
                }
            },
            View::Const(_) => TheoryLit::new(t,sign),
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
            cs: ClauseSet::new(),
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
    pub fn clauses(&mut self, t: AST) -> impl Iterator<Item=&[TheoryLit]> {
        self.cs.clear();

        {
            let Tseitin {
                b, ref mut cs, m, lit_map,
                ref mut tmp, ref mut tmp2, ..} = self;
            let mr = m.get();
            // traverse `t` as a DAG
            self.iter.iter(t, |u| {
                // `u` is a subterm that has never been processed.
                let lmb = LitMapB{lit_map, b: b.clone(), m: m.clone()};
                match mr.view(u) {
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
                        cs.push(&[TheoryLit::new(u, true)]) // clause [true]
                    },
                    _ if u == b.false_ => {
                        // TODO: is this needed? `u` maps to `not true` anyway?
                        cs.push(&[TheoryLit::new(u, false)]) // clause [¬false]
                    },
                    _ => (),
                }
            });
        }

        {
            // unit clause asserting that `t` is true
            let (t,sign) = self.lit_map.unfold_not(t, true);
            self.cs.push(&[(t,sign)]);
        }

        ClauseIter{cs: &self.cs, idx: 0}
    }

}

// iterator over clauses
struct ClauseIter<'a> {
    cs: &'a ClauseSet,
    idx: usize, // in `cs.offsets`
}

mod clauses {
    use super::*;

    impl ClauseSet {
        pub fn new() -> Self {
            Self {lits: Vec::new(), offsets: Vec::new() }
        }

        pub fn clear(&mut self) {
            self.offsets.clear();
            self.lits.clear();
        }

        /// Push a clause
        pub fn push<L>(&mut self, c: &[L])
            where L: Copy + Into<TheoryLit>
        {
            let idx = self.lits.len();
            self.offsets.push((idx, c.len()));
            self.lits.extend(c.iter().map(|&x| x.into()));
        }
    }

    impl<'a> Iterator for ClauseIter<'a> {
        type Item = &'a [TheoryLit];

        fn next(&mut self) -> Option<Self::Item> {
            let cs = self.cs;
            if self.idx >= cs.offsets.len() {
                None
            } else {
                let (off,len) = cs.offsets[self.idx];
                self.idx += 1;
                Some(&cs.lits[off..off+len])
            }
        }
    }
}



