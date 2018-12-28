
use {
    batsmt_parser as parser,
    batsmt_core::{ast, Manager, ast_u32::AST, },
    batsmt_solver::{solver,lit_map},
    batsmt_cc as cc,
    batsmt_tseitin as tseitin,
    fxhash::FxHashMap,
    crate::{parser::Atom, Ctx, Builtins,},
};

/// AST builder for the parser
pub struct AstBuilder<'a> {
    m: &'a mut Ctx,
    b: crate::Builtins,
    sorts: FxHashMap<Atom, (AST, u8)>,
    funs: FxHashMap<Atom, (AST, Vec<AST>, AST)>, // sort
}

mod ast_builder {
    use super::*;

    impl<'a> AstBuilder<'a> {
        /// Create an AST builder that uses the given manager.
        pub fn new(m: &'a mut Ctx) -> Self {
            let b = m.builtins();
            Self {
                m, b,
                funs: FxHashMap::default(),
                sorts: FxHashMap::default(),
            }
        }
    }

    impl<'a> parser::SortBuilder for AstBuilder<'a> {
        type Sort = AST;

        fn get_bool(&self) -> AST { self.b.bool_ }

        fn declare_sort(&mut self, s: Atom, arity: u8) -> AST {
            debug!("declare sort {:?} arity {}", &s, arity);
            if self.sorts.contains_key(&s) {
                panic!("sort {:?} already declared", &s);
            } else {
                let ast = self.m.m.mk_str(&s);
                self.sorts.insert(s, (ast, arity));
                ast
            }
        }
    }

    impl<'a> parser::TermBuilder for AstBuilder<'a> {
        type Term = AST;
        type Fun = AST;
        type Var = AST; // expand let on the fly

        fn var(&mut self, v: AST) -> AST { v }

        fn get_builtin(&self, op: parser::BuiltinOp) -> AST {
            use crate::parser::BuiltinOp::*;
            match op {
                True => self.b.true_,
                False => self.b.false_,
                Imply => self.b.imply_,
                And => self.b.and_,
                Or => self.b.or_,
                Eq => self.b.eq,
                Not => self.b.not_,
                Distinct => self.b.distinct,
            }
        }

        fn declare_fun(&mut self, f: Atom, args: &[AST], ret: AST) -> Self::Fun {
            if self.funs.contains_key(&f) {
                panic!("fun {:?} already declared", &f);
            } else {
                let ast = self.m.m.mk_str(&*f);
                let args = args.iter().map(|t| t.clone()).collect();
                self.funs.insert(f, (ast, args, ret));
                ast
            }
        }

        fn ite(&mut self, _a: AST, _b: AST, _c: AST) -> AST {
            panic!("ite not implemented yet"); // FIXME once we have micro theories
        }

        fn app_fun(&mut self, f: AST, args: &[AST]) -> AST {
            self.m.m.mk_app(f, args)
        }

        fn bind(&mut self, _v: Atom, t: AST) -> AST { t }

        fn let_(&mut self, _: &[(AST,AST)], body: AST) -> AST { body }
    }
}
