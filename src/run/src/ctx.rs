
use {
    batsmt_core::{ast, ast_u32::AST},
    batsmt_hast::{HManager, StrSymbolManager},
    batsmt_theory::{self as theory, LitMapBuiltins},
    batsmt_cc as cc,
    batsmt_solver as solver,
    batsmt_tseitin as tseitin,
};

/// The Manager we use.
pub type M = HManager<StrSymbolManager>;

/// The builtin symbols.
#[derive(Clone,Debug)]
pub struct Builtins {
    pub bool_: AST,
    pub true_: AST,
    pub false_: AST,
    pub not_: AST,
    pub eq: AST,
    pub distinct: AST,
    pub and_: AST,
    pub or_: AST,
    pub imply_: AST,
}

/// The main context.
pub struct Ctx {
    pub m: M,
    pub lmb: LitMapBuiltins,
    pub b: Builtins,
}

pub mod ctx {
    use super::*;

    impl Ctx {
        /// New context.
        pub fn new() -> Self {
            let mut m = HManager::new();
            let b = Builtins::new(&mut m);
            let lmb = b.clone().into();
            Ctx {m, b, lmb}
        }

        /// Copy of builtins
        pub fn builtins<U>(&self) -> U
            where Builtins: Into<U>
        { self.b.clone().into() }

        pub fn lmb(&self) -> LitMapBuiltins { self.lmb.clone() }
    }

    impl theory::BoolLitCtx for Ctx {
        type B = solver::BLit;
    }

    impl ast::HasManager for Ctx {
        type M = M;
        fn m(&self) -> &Self::M { &self.m }
        fn m_mut(&mut self) -> &mut Self::M { &mut self.m }
    }

    // a valid context!
    impl theory::Ctx for Ctx {}
}

mod builtins {
    use super::*;

    impl Builtins {
        /// New builtins structure.
        pub(super) fn new(m: &mut M) -> Self {
            Builtins {
                bool_: m.mk_str("Bool"),
                true_: m.mk_str("true"),
                false_: m.mk_str("false"),
                eq: m.mk_str("="),
                and_: m.mk_str("and"),
                or_: m.mk_str("or"),
                imply_: m.mk_str("=>"),
                not_: m.mk_str("not"),
                distinct: m.mk_str("distinct"),
            }
        }
    }

    impl Into<cc::Builtins<AST>> for Builtins {
        fn into(self) -> cc::Builtins<AST> {
            let Builtins {true_, false_, eq, distinct, not_, ..} = self;
            cc::Builtins {true_,false_,eq,distinct,not_}
        }
    }

    impl Into<tseitin::Builtins> for Builtins {
        fn into(self) -> tseitin::Builtins {
            let Builtins {true_,false_,and_,or_,not_,imply_,eq,distinct, ..} = self;
            tseitin::Builtins {true_,false_,and_,or_,not_,imply_,eq,distinct}
        }
    }

    impl Into<LitMapBuiltins> for Builtins {
        fn into(self) -> LitMapBuiltins {
            let Builtins {true_, false_, not_, bool_, ..} = self;
            LitMapBuiltins {true_,false_,not_,bool_}
        }
    }
}
