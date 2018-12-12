
use {
    batsmt_parser as parser,
    batsmt_core::{ast,AST,StrSymbol},
    fxhash::FxHashMap,
};

type M = ast::Manager<StrSymbol>;

/// AST builder for the parser
pub struct AstBuilder {
    m: M,
    pub bool_: AST,
    pub true_: AST,
    pub false_: AST,
    pub not_: AST,
    pub eq: AST,
    pub distinct: AST,
    pub and_: AST,
    pub or_: AST,
    pub imply_: AST,
    sorts: FxHashMap<String, (AST, u8)>,
    funs: FxHashMap<String, (AST, Vec<AST>, AST)>, // sort
}

mod ast_builder {
    use super::*;

    impl AstBuilder {
        /// Create an AST builder that uses the given manager.
        pub fn new(m: &M) -> Self {
            let m = m.clone();
            Self {
                m: m.clone(),
                bool_: m.mk_str("Bool"),
                true_: m.mk_str("true"),
                false_: m.mk_str("false"),
                eq: m.mk_str("="),
                and_: m.mk_str("and"),
                or_: m.mk_str("or"),
                imply_: m.mk_str("=>"),
                not_: m.mk_str("not"),
                distinct: m.mk_str("distinct"),
                funs: FxHashMap::default(),
                sorts: FxHashMap::default(),
            }
        }
    }

    impl parser::SortBuilder for AstBuilder {
        type Sort = AST;

        fn get_bool(&self) -> AST { self.bool_ }

        fn declare_sort(&mut self, s: String, arity: u8) -> AST {
            debug!("declare sort {:?} arity {}", &s, arity);
            if self.sorts.contains_key(&s) {
                panic!("sort {:?} already declared", &s);
            } else {
                let ast = self.m.get_mut().mk_str(&s);
                self.sorts.insert(s, (ast, arity));
                ast
            }
        }
    }

    impl parser::TermBuilder for AstBuilder {
        type Term = AST;
        type Fun = AST;
        type Var = AST; // expand let on the fly

        fn var(&mut self, v: AST) -> AST { v }

        fn get_builtin(&self, op: parser::BuiltinOp) -> AST {
            use parser::BuiltinOp::*;
            match op {
                Imply => self.imply_,
                And => self.and_,
                Or => self.or_,
                Eq => self.eq,
                Not => self.not_,
                Distinct => self.distinct,
            }
        }

        fn declare_fun(&mut self, f: String, args: &[AST], ret: AST) -> Self::Fun {
            if self.funs.contains_key(&f) {
                panic!("fun {:?} already declared", &f);
            } else {
                let ast = self.m.get_mut().mk_string(f.clone());
                let args = args.iter().map(|t| t.clone()).collect();
                self.funs.insert(f, (ast, args, ret));
                ast
            }
        }

        fn ite(&mut self, a: AST, b: AST, c: AST) -> AST {
            panic!("ite not implemented yet"); // FIXME once we have micro theories
        }

        fn app_fun(&mut self, f: AST, args: &[AST]) -> AST {
            self.m.get_mut().mk_app(f, args)
        }

        fn bind(&mut self, _v: String, t: AST) -> AST { t }

        fn let_(&mut self, _: &[(AST,AST)], body: AST) -> AST { body }
    }

}
