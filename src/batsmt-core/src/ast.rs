
//! AST manager
//!
//! The AST manager stores AST nodes, referred to via `ID`. These nodes can
//! be used to represent sorts, terms, formulas, theory terms, etc.

use smallvec::SmallVec;
use super::symbol::Symbol;
use fxhash::FxHashMap;
use std::collections::hash_map::Entry;

/* Note: positive IDs are applications, negative IDs are symbols
 */
/// The unique identifier of an AST node.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd,Debug)]
pub struct AST(i32);

/// Number of arguments for a "small" term application
pub const N_SMALL_APP : usize = 3;

/// The definition of an AST node, as seen from outside
#[derive(Debug,Copy,Clone)]
pub enum View<'a> {
    Const(&'a Symbol),
    App {
        f: AST,
        args: &'a [AST],
    }
}

#[derive(Clone,Eq,PartialEq,Hash,Debug)]
struct AppKey {
    f: AST,
    args: SmallVec<[AST; N_SMALL_APP]>,
}

pub struct AstManager {
    consts: Vec<Symbol>,
    apps: Vec<AppKey>,
    tbl_app: FxHashMap<AppKey, AST>, // for hashconsing
}

impl AstManager {
    /// Create a new AST manager
    pub fn new() -> Self {
        AstManager {
            consts: Vec::with_capacity(512),
            apps: Vec::with_capacity(1_024),
            tbl_app: FxHashMap::default(),
        }
    }

    /// View the definition of an AST node
    #[inline]
    pub fn view(&self, ast: AST) -> View {
        if ast.0 < 0 {
            let s = & self.consts[((- ast.0)-1) as usize];
            View::Const(s)
        } else {
            let AppKey {f, args} = & self.apps[ast.0 as usize];
            View::App {f: *f, args: &args}
        }
    }

    fn mk_symbol(&mut self, s: Symbol) -> AST {
        let n = - (1 + self.consts.len() as i32);
        self.consts.push(s);
        AST(n)
    }

    /// Make a named symbol.
    ///
    /// Note that calling this function twice with the same string
    /// will result in two distinct symbols (as if the second one
    /// was shadowing the first). Use an auxiliary hashtable if
    /// you want sharing.
    #[inline]
    pub fn mk_const(&mut self, s: &str) -> AST {
        self.mk_symbol(Symbol::mk_str(s.to_string()))
    }

    // Add or retrieve the unique term with this definition
    fn hashcons(&mut self, app: AppKey) -> AST {
        // borrow multiple fields
        let AstManager {ref mut apps, ref mut tbl_app,..} = self;
        match tbl_app.entry(app) {
            Entry::Vacant(ve) => {
                // insert
                let n = apps.len();
                let node2 = ve.key().clone(); // copy the key
                apps.push(node2);
                let ast = AST(n as i32);
                ve.insert(ast);
                ast
            },
            Entry::Occupied(e) => *e.get(),
        }
    }

    pub fn mk_app(&mut self, f: AST, args: &[AST]) -> AST {
        // FIXME: if already present, we should not need to copy :s
        // this will most likely require unsafe and raw pointers. To be
        // assessed later with proper benchmarks.
        let app = AppKey{f, args: SmallVec::from_slice(args)};
        self.hashcons(app)
    }
}
