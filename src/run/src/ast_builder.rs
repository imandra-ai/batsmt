
use {
    batsmt_parser as parser,
    batsmt_core::{ast,AST,StrSymbol},
    batsmt_solver::{solver,lit_map},
    batsmt_cc as cc,
    batsmt_tseitin as tseitin,
    fxhash::FxHashMap,
};

type Atom = parser::Atom;
type M = ast::Manager<StrSymbol>;

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

/// AST builder for the parser
pub struct AstBuilder {
    m: M,
    b: Builtins,
    sorts: FxHashMap<Atom, (AST, u8)>,
    funs: FxHashMap<Atom, (AST, Vec<AST>, AST)>, // sort
}

mod ast_builder {
    use super::*;

    impl AstBuilder {
        /// Create an AST builder that uses the given manager.
        pub fn new(m: &M) -> Self {
            let m = m.clone();
            Self {
                m: m.clone(),
                b: Builtins::new(&m),
                funs: FxHashMap::default(),
                sorts: FxHashMap::default(),
            }
        }

        /// Convert builtins into `B`
        pub fn builtins<B>(&self) -> B where Builtins: Into<B>
        {
            let b = self.b.clone();
            b.into()
        }
    }

    impl Builtins {
        pub fn new(m: &M) -> Self {
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

    impl Into<solver::Builtins> for Builtins {
        fn into(self) -> solver::Builtins {
            let Builtins {true_, false_, bool_, not_,..} = self;
            solver::Builtins {bool_,true_,false_,not_}
        }
    }

    impl Into<cc::Builtins> for Builtins {
        fn into(self) -> cc::Builtins {
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

    impl Into<lit_map::Builtins> for Builtins {
        fn into(self) -> lit_map::Builtins {
            let Builtins {true_, false_, not_, bool_, ..} = self;
            lit_map::Builtins {true_,false_,not_,bool_}
        }
    }

    impl parser::SortBuilder for AstBuilder {
        type Sort = AST;

        fn get_bool(&self) -> AST { self.b.bool_ }

        fn declare_sort(&mut self, s: Atom, arity: u8) -> AST {
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
                let ast = self.m.get_mut().mk_str(&*f);
                let args = args.iter().map(|t| t.clone()).collect();
                self.funs.insert(f, (ast, args, ret));
                ast
            }
        }

        fn ite(&mut self, _a: AST, _b: AST, _c: AST) -> AST {
            panic!("ite not implemented yet"); // FIXME once we have micro theories
        }

        fn app_fun(&mut self, f: AST, args: &[AST]) -> AST {
            self.m.get_mut().mk_app(f, args)
        }

        fn bind(&mut self, _v: Atom, t: AST) -> AST { t }

        fn let_(&mut self, _: &[(AST,AST)], body: AST) -> AST { body }
    }
}
