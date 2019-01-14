
//! Notion of mapping between (boolean) terms and SAT literals

use {
    batsmt_core::{
        ast::{View, Manager, },
        ast_u32::{AST, },
    },
    crate::{BoolLit, },
};

/// Builtin symbols required for this basic interface.
#[derive(Clone,Debug)]
pub struct Builtins {
    pub bool_: AST, // the boolean sort
    pub true_: AST, // term for `true`
    pub false_: AST, // term for `false`
    pub not_: AST, // used to traverse negation automatically
}

impl Builtins {
    /// Unfolds negations, returns unsigned term + number of negations.
    ///
    /// Given `t = not^n(u)`, this returns `u, not^n(sign)`.
    /// This way `u` is never a negation.
    pub fn unfold_not<M>(&self, m: &M, t: &AST, mut sign: bool) -> (AST, bool)
        where M: ManagerU32
    {
        let mut t = t;
        loop {
            match m.view(t) {
                View::App {f, args} if f == self.not_ => {
                    // flip sign and recurse
                    t = &args[0];
                    sign = !sign;
                },
                _ if t == &self.false_ => {
                    // `false` is just `not true`
                    t = &self.true_;
                    sign = !sign;
                    break;
                }
                _ => break,
            }
        }
        (t.clone(),sign)
    }
}

/// A mapping between boolean literals, and terms of boolean type.
pub trait LitMap<B:BoolLit> {
    /// Create a new `LitMap`.
    fn new(b: Builtins) -> Self where Self : Sized;

    /// Access the set of builtins.
    fn b(&self) -> &Builtins;

    /// Shortcut: unfold negation.
    #[inline(always)]
    fn unfold_not<M>(&self, m: &M, t: &AST, sign: bool) -> (AST, bool)
        where M: ManagerU32
    {
        self.b().unfold_not(m, t, sign)
    }

    /// Find which literal this term maps to, if any.
    fn get_term<M>(&self, m: &M, t: &AST, sign: bool) -> Option<B>
        where M: ManagerU32;

    /// Find which literal this term maps to, or create a new one using `f`.
    ///
    /// `f` is a generator of fresh boolean literals.
    /// `bidir` if true, remember that this literal maps to this term (see `add_term`).
    fn get_term_or_else<M, F>(&mut self, m: &M, t: &AST, sign: bool, bidir: bool, f: F) -> B
        where M: ManagerU32,
              F: FnOnce() -> B;

    /// Add a mapping from `t` to `lit`.
    ///
    /// if `bidir` also remember that `lit` maps to `t`.
    fn add_term<M>(&mut self, m: &M, t: &AST, lit: B, bidir: bool)
        where M: ManagerU32;

    /// Map the given literal into a signed term, if any.
    ///
    /// This works only if `lit` (or its negation) was added earlier using
    /// `add_term` with `bidir=true`.
    fn map_lit(&self, lit: B) -> Option<(AST, bool)>;
}
