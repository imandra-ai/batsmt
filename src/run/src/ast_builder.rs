
use {
    batsmt_parser as parser,
    batsmt_core::{ast_u32::AST, },
    fxhash::FxHashMap,
    crate::{parser::Atom, Ctx, },
};

/// AST builder for the parser
pub struct AstBuilder<'a> {
    m: &'a mut Ctx,
    b: crate::Builtins,
    sorts: FxHashMap<Atom, (AST, u8)>,
    funs: FxHashMap<Atom, (AST, Vec<AST>, AST)>, // sort
}

mod ast_builder {
    use {super::*, batsmt_core::Manager};

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
                let ast = self.m.m.mk_str(&s, None);
                self.sorts.insert(s, (ast, arity));
                ast
            }
        }
    }

    #[derive(Clone,Debug)]
    pub struct Fun { f: AST, ty_ret: AST }

    impl<'a> parser::TermBuilder for AstBuilder<'a> {
        type Term = AST;
        type Fun = Fun;
        type Var = AST; // expand let on the fly

        fn var(&mut self, v: AST) -> AST { v }

        fn app_op(&mut self, op: parser::BuiltinOp, args: &[AST]) -> AST {
            use crate::parser::BuiltinOp::*;
            let f = match op {
                True => self.b.true_,
                False => self.b.false_,
                Imply => self.b.imply_,
                And => self.b.and_,
                Or => self.b.or_,
                Eq => self.b.eq,
                Not => self.b.not_,
                Distinct => self.b.distinct,
            };
            self.m.m.mk_app(f, args, Some(self.b.bool_))
        }

        fn declare_fun(&mut self, f: Atom, args: &[AST], ret: AST) -> Self::Fun {
            if self.funs.contains_key(&f) {
                panic!("fun {:?} already declared", &f);
            } else {
                let ty = if args.len() == 0 { Some(ret) } else { None };
                let ast = self.m.m.mk_str(&*f, ty);
                let args = args.iter().map(|t| t.clone()).collect();
                self.funs.insert(f, (ast, args, ret));
                Fun {f: ast, ty_ret: ret}
            }
        }

        fn declare_cstor(&mut self, f: Atom, args: &[AST], ret: AST) -> Self::Fun {
            let f = self.declare_fun(f, args, ret);
            self.m.set_cstor(&f.f);
            f
        }

        fn ite(&mut self, a: AST, b: AST, c: AST) -> AST {
            let f = self.b.ite;
            self.m.m.mk_app(f, &[a,b,c], self.m.m.ty(&b))
        }

        fn app_fun(&mut self, f: Self::Fun, args: &[AST]) -> AST {
            self.m.m.mk_app(f.f, args, Some(f.ty_ret))
        }

        fn bind(&mut self, _v: Atom, t: AST) -> AST { t }

        fn let_(&mut self, _: &[(AST,AST)], body: AST) -> AST { body }
    }
}
