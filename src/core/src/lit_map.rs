
//! Mapping between (boolean) terms and SAT literals

use {
    crate::{symbol::Symbol, ast::{self,AST}},
    batsat::{Lit as BLit, LMap},
};

/// Bidirectional mapping between literals and terms
pub struct LitMap<S:Symbol> {
    m: ast::Manager<S>,
    builtins: Builtins,
    term_to_lit: ast::HashMap<BLit>,
    lit_to_term: LMap<(AST,bool)>,
}

/// Builtin symbols required for this basic interface
#[derive(Copy,Clone)]
pub struct Builtins {
    pub bool_: AST, // the boolean sort
    pub true_: AST, // term for `true`
    pub false_: AST, // term for `false`
}

impl<S:Symbol> LitMap<S> {
    /// Create a new mapping.
    ///
    /// Note that `builtins` need to be provided.
    pub fn new(m: &ast::Manager<S>, b: Builtins) -> Self {
        LitMap {
            builtins:b, m: m.clone(), term_to_lit: ast::HashMap::default(),
            lit_to_term: LMap::new(),
        }
    }

    /// Add a bidirectional mapping from `t` to `lit`
    pub fn add_term(&mut self, t: AST, lit: BLit) {
        debug_assert!(! self.term_to_lit.contains_key(&t));
        let pad = (AST::SENTINEL, true); // used to fill the map
        self.lit_to_term.insert(lit, (t, true), pad);
        self.lit_to_term.insert(! lit, (t, false), pad);
        self.term_to_lit.insert(t, lit);
    }

    /// Map the given term to a literal
    pub fn map_term(&self, t: AST, sign: bool) -> Option<BLit> {
        self.term_to_lit.get(&t).map(|lit| if sign { *lit } else { ! *lit })
    }

    /// Map the given literal into a signed term
    pub fn map_lit(&self, lit: BLit) -> (AST, bool) {
        self.lit_to_term[lit]
    }
}


