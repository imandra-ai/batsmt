
//! Mapping between (boolean) terms and SAT literals

use {
    batsmt_core::{
        ast::{self, AstMap},
        ast_u32::{AST, ManagerU32, },
    },
    batsmt_theory::{self as theory, BoolLit, },
    batsat::{LMap, },
    crate::BLit,
};

// re-exports
pub use {
    batsmt_theory::LitMapBuiltins as Builtins,
};

/// Bidirectional mapping between SAT literals (`BLit`) and terms.
pub struct SatLitMap {
    b: Builtins,
    term_to_lit: ast::HashMap<AST,BLit>,
    theory_lits: Vec<(AST,BLit)>, // only bidir terms
    lit_to_term: LMap<(AST,bool)>,
}

impl theory::LitMap<BLit> for SatLitMap {
    fn new(b: Builtins) -> Self {
        assert_ne!(b.true_, b.false_); // sanity check
        SatLitMap {
            b,
            term_to_lit: ast::HashMap::new(),
            lit_to_term: LMap::new(),
            theory_lits: vec!(),
        }
    }

    #[inline(always)]
    fn b(&self) -> &Builtins { &self.b }

    fn get_term<M>(&self, m: &M, t: &AST, sign: bool) -> Option<BLit>
        where M: ManagerU32
    {
        let (t, sign) = self.b.unfold_not(m, t, sign);
        self.term_to_lit.get(&t).map(|lit| lit.apply_sign(sign))
    }

    fn get_term_or_else<M, F>(
        &mut self, m: &M, t: &AST, sign: bool, bidir: bool, f: F
    ) -> BLit
        where M: ManagerU32,
              F: FnOnce() -> BLit
    {
        let (t, sign) = self.b.unfold_not(m, t, sign);
        let lit =
            self.term_to_lit.get(&t).map(|lit| *lit)
            .unwrap_or_else(|| {
                let lit = f();
                // remember mapping
                self.add_term_normalized(m, t, lit, bidir);
                lit
            });
        lit.apply_sign(sign)
    }

    fn add_term<M>(&mut self, m: &M, t: &AST, mut lit: BLit, bidir: bool)
        where M: ManagerU32
    {
        let (t, sign) = self.b.unfold_not(m, &t, true);
        if !sign {
            lit = !lit; // mapping `not t` to `a42` means mapping `t` to `¬a42`
        };
        self.add_term_normalized(m, t, lit, bidir)
    }

    fn map_lit(&self, lit: BLit) -> Option<(AST, bool)> {
        if self.lit_to_term.has(lit.0) {
            let pair = self.lit_to_term[lit.0];
            // is it a real value?
            if pair.0 == AST::SENTINEL { None } else { Some(pair) }
        } else {
            None
        }
    }
}

impl SatLitMap {
    // Add `t <-> lit`.
    //
    // assume `t` is not a negation
    fn add_term_normalized<M>(&mut self, m: &M, t: AST, lit: BLit, bidir: bool)
        where M: ManagerU32
    {
        assert_ne!(t, AST::SENTINEL); // breaks invariants
        debug_assert_eq!(t, self.b.unfold_not(m,&t,true).0);
        debug_assert!(! self.term_to_lit.contains(&t));
        if bidir {
            let pad = (AST::SENTINEL, true); // used to fill the map
            self.lit_to_term.insert(lit.0, (t, true), pad);
            self.lit_to_term.insert(! lit.0, (t, false), pad);
            self.theory_lits.push((t, lit));
        }
        self.term_to_lit.insert(t, lit);
    }

    /// Iterate over all know theory literals.
    pub fn iter_theory_lits<'a>(&'a self) -> impl Iterator<Item=(AST,BLit)> + 'a {
        self.theory_lits.iter().cloned()
    }
}
