
//! Tseitin Transformation

use {
    batsmt_core::{
        ast::{self,AST,View,iter_dag::State as AstIter},Symbol,
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
    tmp: Vec<(AST,bool)>, // temp clause
    lit_map: LitMap<S>,
    cs: ClauseSet, // clauses
}

#[derive(Clone)]
struct ClauseSet {
    lits: Vec<(AST,bool)>, // clause lits
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
}

impl<S:Symbol> Tseitin<S> {
    /// Create a new Tseitin transformation
    pub fn new(m: &M<S>, lit_map: &LitMap<S>, b: Builtins) -> Self {
        Self {
            b, m: m.clone(),
            lit_map: lit_map.clone(),
            tmp: Vec::new(),
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
    pub fn clauses(&mut self, t: AST) -> impl Iterator<Item=&[(AST,bool)]> {
        self.cs.clear();

        // traverse `t` as a DAG
        self.iter.iter(t, |u| {
            // `u` is a subterm that has never been processed.

            let mr = self.m.get();
            match mr.view(u) {
                View::App {f, args} if f == self.b.not_ => {
                    debug_assert_eq!(1, args.len());
                    let lit = self.lit_map.find_signed(t);
                },
                _ if u == self.b.true_ => {
                    panic!("true") // FIXME
                },
                _ if u == self.b.false_ => {
                    panic!("false") // FIXME
                },
                _ => (),

            }
        });

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
        pub fn push(&mut self, c: &[(AST,bool)]) {
            let idx = self.lits.len();
            self.offsets.push((idx, c.len()));
            self.lits.extend_from_slice(c);
        }
    }

    impl<'a> Iterator for ClauseIter<'a> {
        type Item = &'a [(AST,bool)];

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



