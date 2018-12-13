
//! Mapping between (boolean) terms and SAT literals

use {
    crate::{
        symbol::Symbol, ast::{self,AST,View},
        util::{Shared,SharedRef,SharedRefMut},
    },
    batsat::{Lit as BLit, Var as BVar, LMap},
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

struct LitMapCell<S:Symbol> {
    m: ast::Manager<S>,
    b: Builtins,
    term_to_lit: ast::HashMap<BLit>,
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
    fn get(&self) -> SharedRef<LitMapCell<S>> { self.0.borrow() }

    #[inline(always)]
    fn get_mut(&self) -> SharedRefMut<LitMapCell<S>> { self.0.borrow_mut() }

    /// Add a bidirectional mapping from `t` to `lit`
    pub fn add_term(&self, t: AST, lit: BLit) {
        self.get_mut().add_term(t,lit)
    }

    /// Find which literal this term maps to, if any
    pub fn get_term(&self, t: AST, sign: bool) -> Option<BLit> {
        self.get().get_term(t,sign)
    }

    /// Find which literal this term maps to, or create a new one using `f`
    ///
    /// `f` is a generator of fresh boolean variables.
    pub fn get_term_or_else<F>(&self, t: AST, sign: bool, f: F) -> BLit
        where F: FnOnce() -> BVar
    {
        self.get_mut().get_term_or_else(t,sign,f)
    }

    /// Map the given literal into a signed term
    pub fn map_lit(&self, lit: BLit) -> (AST, bool) {
        self.get().lit_to_term[lit]
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

    fn get_term_or_else<F>(&mut self, t: AST, sign: bool, f: F) -> BLit
        where F: FnOnce() -> BVar
    {
        let (t, sign) = self.unfold_not(t, sign);
        let lit =
            self.term_to_lit.get(&t).map(|lit| *lit)
            .unwrap_or_else(|| {
                let lit = BLit::new(f(), true);
                // remember mapping
                self.add_term_normalized(t, lit);
                lit
            });
        lit_apply_sign(lit, sign)
    }

    // Add a bidirectional mapping from `t` to `lit`
    fn add_term(&mut self, t: AST, mut lit: BLit) {
        let (t, sign) = self.unfold_not(t, true);
        if !sign {
            lit = !lit; // mapping `not t` to `a42` means mapping `t` to `¬a42`
        };
        self.add_term_normalized(t, lit)
    }

    // assume `t` is not a negation
    fn add_term_normalized(&mut self, t: AST, lit: BLit) {
        debug_assert_eq!(t, self.unfold_not(t,true).0);
        debug_assert!(! self.term_to_lit.contains_key(&t));
        let pad = (AST::SENTINEL, true); // used to fill the map
        self.lit_to_term.insert(lit, (t, true), pad);
        self.lit_to_term.insert(! lit, (t, false), pad);
        self.term_to_lit.insert(t, lit);
    }
}
