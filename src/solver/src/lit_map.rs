
//! Mapping between (boolean) terms and SAT literals

use {
    batsmt_core::{
        symbol::Symbol, ast::{self,AST,View},
        Shared,SharedRef,SharedRefMut,
    },
    batsat::{Var as BVar, LMap},
    crate::blit::BLit,
};

/// Builtin symbols required for this basic interface
#[derive(Copy,Clone,Debug)]
pub struct Builtins {
    pub bool_: AST, // the boolean sort
    pub true_: AST, // term for `true`
    pub false_: AST, // term for `false`
    pub not_: AST, // used to traverse negation automatically
}

/// Bidirectional mapping between literals and terms
#[derive(Clone)]
pub struct LitMap<S:Symbol>(Shared<LitMapCell<S>>);

pub struct LitMapCell<S:Symbol> {
    m: ast::Manager<S>,
    b: Builtins,
    term_to_lit: ast::HashMap<BLit>,
    theory_lits: Vec<(AST,BLit)>, // only bidir terms
    lit_to_term: LMap<(AST,bool)>,
}

/// Keep or flip polarity of `lit` based on sign
#[inline(always)]
pub fn lit_apply_sign(lit: BLit, sign: bool) -> BLit {
    if sign { lit } else { ! lit }
}

impl<S:Symbol> LitMap<S> {
    /// Create a new mapping.
    ///
    /// Note that `builtins` need to be provided.
    pub fn new(m: &ast::Manager<S>, b: Builtins) -> Self {
        let cell = LitMapCell::new(m.clone(), b);
        LitMap(Shared::new(cell))
    }

    #[inline(always)]
    pub fn get(&self) -> SharedRef<LitMapCell<S>> { self.0.borrow() }

    #[inline(always)]
    pub fn get_mut(&self) -> SharedRefMut<LitMapCell<S>> { self.0.borrow_mut() }

    /// Add a mapping from `t` to `lit`
    ///
    /// if `bidir` also remember that `lit` maps to `t`
    pub fn add_term(&self, t: AST, lit: BLit, bidir: bool) {
        self.get_mut().add_term(t,lit,bidir)
    }

    /// Find which literal this term maps to, if any
    pub fn get_term(&self, t: AST, sign: bool) -> Option<BLit> {
        self.get().get_term(t,sign)
    }

    /// Find which literal this term maps to, or create a new one using `f`
    ///
    /// `f` is a generator of fresh boolean variables.
    /// `bidir` if true, remember that this literal maps to this term
    pub fn get_term_or_else<F>(&self, t: AST, sign: bool, bidir: bool, f: F) -> BLit
        where F: FnOnce() -> BVar
    {
        self.get_mut().get_term_or_else(t,sign,bidir,f)
    }

    /// Map the given literal into a signed term
    pub fn map_lit(&self, lit: BLit) -> Option<(AST, bool)> {
        let r = self.get();
        if r.lit_to_term.has(lit.0) {
            let pair = r.lit_to_term[lit.0];
            // is it a real value?
            if pair.0 == AST::SENTINEL { None } else { Some(pair) }
        } else {
            None
        }
    }

    /// Given `t = not^n(u)`, returns `u, not^n(sign)`.
    ///
    /// This way `u` is never a negation.
    pub fn unfold_not(&self, t: AST, sign: bool) -> (AST, bool) {
        self.get().unfold_not(t,sign)
    }
}

impl<S:Symbol> LitMapCell<S> {
    fn new(m: ast::Manager<S>, b: Builtins) -> Self {
        assert_ne!(b.true_, b.false_); // sanity check
        LitMapCell {
            b,
            m: m,
            term_to_lit: ast::HashMap::default(),
            lit_to_term: LMap::new(),
            theory_lits: vec!(),
        }
    }

    // given `t = not^n(u)`, returns `u, not^n(sign)`. This way `u` is never
    // a negation.
    fn unfold_not(&self, mut t: AST, mut sign: bool) -> (AST, bool) {
        let mr = self.m.get();
        loop {
            match mr.view(t) {
                View::App {f, args} if f == self.b.not_ => {
                    // flip sign and recurse
                    t = args[0];
                    sign = !sign;
                },
                _ if t == self.b.false_ => {
                    // `false` is just `not true`
                    t = self.b.true_;
                    sign = !sign;
                    break;
                }
                _ => break,
            }
        }
        (t,sign)
    }

    fn get_term(&self, t: AST, sign: bool) -> Option<BLit> {
        let (t, sign) = self.unfold_not(t, sign);
        self.term_to_lit.get(&t).map(|lit| lit_apply_sign(*lit, sign))
    }

    fn get_term_or_else<F>(&mut self, t: AST, sign: bool, bidir: bool, f: F) -> BLit
        where F: FnOnce() -> BVar
    {
        let (t, sign) = self.unfold_not(t, sign);
        let lit =
            self.term_to_lit.get(&t).map(|lit| *lit)
            .unwrap_or_else(|| {
                let lit = BLit::from_var(f(), true);
                // remember mapping
                self.add_term_normalized(t, lit, bidir);
                lit
            });
        lit_apply_sign(lit, sign)
    }

    // Add a bidirectional mapping from `t` to `lit`
    fn add_term(&mut self, t: AST, mut lit: BLit, bidir: bool) {
        let (t, sign) = self.unfold_not(t, true);
        if !sign {
            lit = !lit; // mapping `not t` to `a42` means mapping `t` to `¬a42`
        };
        self.add_term_normalized(t, lit, bidir)
    }

    // assume `t` is not a negation
    fn add_term_normalized(&mut self, t: AST, lit: BLit, bidir: bool) {
        assert_ne!(t, AST::SENTINEL); // breaks invariants
        debug_assert_eq!(t, self.unfold_not(t,true).0);
        debug_assert!(! self.term_to_lit.contains_key(&t));
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
