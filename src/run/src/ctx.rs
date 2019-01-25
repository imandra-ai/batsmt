
use {
    batsmt_core::{ast, ast_u32::AST, Manager, AstView},
    batsmt_hast::{HManager, StrSymbolManager},
    batsmt_theory::{self as theory, LitMapBuiltins},
    batsmt_cc::{self as cc, CCView},
    batsmt_solver as solver,
    batsmt_pretty as pp,
    batsmt_tseitin::{self as tseitin, View as FView, }
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
    pub ite: AST,
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

    impl tseitin::Ctx for Ctx {
        fn view_as_formula(&self, t: AST) -> FView<AST> {
            if t == self.b.true_ { tseitin::View::Bool(true) }
            else if t == self.b.false_ { tseitin::View::Bool(true) }
            else {
                match self.m.view(&t) {
                    AstView::Const(_) => FView::Atom(t),
                    AstView::App{f, args} if *f == self.b.not_ => {
                        debug_assert_eq!(args.len(), 1);
                        FView::Not(args[0])
                    },
                    AstView::App{f, args} if *f == self.b.eq => {
                        debug_assert_eq!(args.len(), 2);
                        FView::Eq(args[0], args[1])
                    },
                    AstView::App{f, args} if *f == self.b.distinct => {
                        FView::Distinct(args)
                    },
                    AstView::App{f, args} if *f == self.b.imply_ => {
                        FView::Imply(args)
                    },
                    AstView::App{f, args} if *f == self.b.and_ => {
                        FView::And(args)
                    },
                    AstView::App{f, args} if *f == self.b.or_ => {
                        FView::Or(args)
                    },
                    AstView::App{f, args} if *f == self.b.ite => {
                        debug_assert_eq!(args.len(), 3);
                        FView::Ite(args[0], args[1], args[2])
                    },
                    AstView::App{..} => FView::Atom(t),
                }
            }
        }
        fn mk_formula(&mut self, v: FView<AST>) -> AST {
            match v {
                FView::Atom(t) => t,
                FView::Bool(true) => self.b.true_,
                FView::Bool(false) => self.b.false_,
                FView::Eq(t,u) if t == u => self.b.true_,
                FView::Eq(t,u) => self.m.mk_app(self.b.eq, &[t, u]),
                FView::Distinct(args) => self.m.mk_app(self.b.distinct, args),
                FView::Ite(a,b,c) => self.m.mk_app(self.b.ite, &[a,b,c]),
                FView::Not(t) => {
                    match self.view_as_formula(t) {
                        FView::Bool(true) => self.b.false_,
                        FView::Bool(false) => self.b.true_,
                        FView::Not(u) => u,
                        _ => self.m.mk_app(self.b.not_, &[t]),
                    }
                },
                FView::And(args) => {
                    if args.len() == 0 { self.b.true_ }
                    else if args.len() == 1 { args[0] }
                    else { self.m.mk_app(self.b.and_, args) }
                },
                FView::Or(args) => {
                    if args.len() == 0 { self.b.false_ }
                    else if args.len() == 1 { args[0] }
                    else { self.m.mk_app(self.b.or_, args) }
                },
                FView::Imply(args) => {
                    assert_ne!(args.len(), 0);
                    if args.len() == 1 { args[0] }
                    else { self.m.mk_app(self.b.imply_, args) }
                },
            }
        }
    }

    impl ast::HasManager for Ctx {
        type M = M;
        fn m(&self) -> &Self::M { &self.m }
        fn m_mut(&mut self) -> &mut Self::M { &mut self.m }
    }

    impl pp::Pretty1<AST> for Ctx {
        fn pp1_into(&self, t: &AST, ctx: &mut pp::Ctx) {
            ast::pp_ast(self, t, &mut |s,ctx| { ctx.display(s); }, ctx);
        }
    }

    // a valid context!
    impl theory::Ctx for Ctx {
        fn pp_ast(&self, t: &AST, ctx: &mut pp::Ctx) {
            ctx.pp1(&self.m, t);
        }
    }

    impl cc::Ctx for Ctx {
        type Fun = cc::intf::Void;

        fn get_bool_term(&self, b: bool) -> AST {
            if b { self.b.true_ } else { self.b.false_ }
        }

        fn view_as_cc_term<'a>(&'a self, t: &'a AST) -> CCView<'a,Self::Fun,AST> {
            if *t == self.b.true_ {
                CCView::Bool(true)
            } else if *t == self.b.false_ {
                CCView::Bool(false)
            } else if self.m.is_const(t) {
                CCView::Opaque(t) // shortcut
            } else {
                match self.m.view(t) {
                    AstView::Const(_) => CCView::Opaque(t),
                    AstView::App{f, args} if *f == self.b.eq => {
                        debug_assert_eq!(args.len(), 2);
                        CCView::Eq(&args[0], &args[1])
                    },
                    AstView::App{f, args} if *f == self.b.distinct => {
                        CCView::Distinct(args)
                    },
                    AstView::App{f,args} => CCView::ApplyHO(f,args),
                }
            }
        }
    }

    impl cc::HasIte<AST> for Ctx {
        fn view_as_ite<'a>(&'a self, t: &'a AST) -> cc::IteView<'a, AST> {
            match self.m.view(t) {
                AstView::App{f, args} if *f == self.b.ite => {
                    debug_assert_eq!(args.len(), 3);
                    cc::IteView::Ite(&args[0], &args[1], &args[2])
                },
                _ => cc::IteView::Other(t),
            }
        }
    }
}

mod builtins {
    use super::*;

    impl Builtins {
        /// New builtins structure.
        pub(super) fn new(m: &mut M) -> Self {
            Builtins {
                ite: m.mk_str("ite"),
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

    impl Into<LitMapBuiltins> for Builtins {
        fn into(self) -> LitMapBuiltins {
            let Builtins {true_, false_, not_, bool_, ..} = self;
            LitMapBuiltins {true_,false_,not_,bool_}
        }
    }
}
