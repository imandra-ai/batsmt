
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
                match mr.view(u) {
                    View::App {f, args} if f == b.not_ => {
                        debug_assert_eq!(1, args.len());
                        () // nothing to do here
                    },
                    View::App {f, args} if f == b.and_ => {
                        // obtain literals for subterms of the `and` into `tmp`
                        tmp.clear();
                        for t in args.iter() {
                            tmp.push(lit_map.unfold_not(*t, true).into());
                        }
                        let lit_and: TheoryLit = u.into();

                        // `lit_and => args[i]`
                        for sub in tmp.iter() {
                            cs.push(&[!lit_and, *sub]);
                        }
                        // `args[i] ==> lit_and`
                        {
                            tmp2.clear();
                            for sub in tmp.iter() { tmp2.push(!*sub) }
                            tmp2.push(lit_and);
                            cs.push(&tmp2);
                        }
                    },
                    _ if u == b.true_ => {
                        cs.push(&[(u, true)]) // clause [true]
                    },
                    _ if u == b.false_ => {
                        cs.push(&[(u, false)]) // clause [¬false]
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



