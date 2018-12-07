
// A test binary

extern crate env_logger;
extern crate batsmt_core;
extern crate batsmt_cc;
extern crate batsmt_parser;
extern crate fxhash;
#[macro_use] extern crate log;

use {
    std::{env,fs,error::Error},
    batsmt_core::{ast,AST},
    batsmt_cc::CC,
    batsmt_parser as parser,
};

/// Simple representation of terms, sorts, etc.
mod parse_ast {
    use {
        fxhash::FxHashMap,
        std::{ops::Deref,rc::Rc},
        parser::types::{self,Op},
    };

    #[derive(Debug,Eq,PartialEq,Hash)]
    pub struct SortCell {
        name: String,
        arity: u8,
    }

    /// A sort
    #[derive(Debug,Clone,Eq,PartialEq,Hash)]
    pub struct Sort(Rc<SortCell>);

    impl Sort {
        /// New sort
        fn new(name: String, arity: u8) -> Self {
            Sort(Rc::new(SortCell{name, arity}))
        }
    }
    impl Deref for Sort {
        type Target = SortCell;
        fn deref(&self) -> &Self::Target { &self.0 }
    }

    #[derive(Debug,Eq,PartialEq,Hash)]
    pub struct FunCell {
        name: String,
        args: Option<Vec<Sort>>,
        ret: Sort,
    }

    /// A function
    #[derive(Debug,Clone,Eq,PartialEq,Hash)]
    pub struct Fun(Rc<FunCell>);

    impl Fun {
        /// New fun
        fn new(name: String, args: Option<Vec<Sort>>, ret: Sort) -> Self {
            Fun(Rc::new(FunCell {name, args, ret}))
        }
    }
    impl Deref for Fun {
        type Target = FunCell;
        fn deref(&self) -> &Self::Target { &self.0 }
    }

    #[derive(Debug,Eq,PartialEq,Hash)]
    pub enum TermCell {
        App(Fun, Vec<Term>),
        Ite(Term,Term,Term),
    }

    /// A term
    #[derive(Debug,Clone,Eq,PartialEq,Hash)]
    pub struct Term(Rc<TermCell>);

    impl Term {
        fn app(f: Fun, args: Vec<Term>) -> Self {
            Term(Rc::new(TermCell::App(f, args)))
        }
        fn app_ref(f: Fun, args: &[Term]) -> Self {
            let args = args.iter().map(|t| t.clone()).collect();
            Term::app(f, args)
        }
        fn app0(f: Fun) -> Self {
            Term(Rc::new(TermCell::App(f, Vec::new())))
        }
        fn ite(a: Term, b: Term, c: Term) -> Self {
            Term(Rc::new(TermCell::Ite(a,b,c)))
        }
    }
    impl Deref for Term {
        type Target = TermCell;
        fn deref(&self) -> &Self::Target { &self.0 }
    }

    /// The builder used for holding context and parsing
    pub struct Builder {
        bool_: Sort,
        and_ : Fun,
        or_ : Fun,
        imply_ : Fun,
        eq : Fun,
        not_ : Fun,
        // scoping for `let`
        vars: FxHashMap<String, Term>,
        scopes: Vec<Vec<(String, Option<Term>)>>, // open scopes (with previous binding)
    }

    impl Builder {
        /// New builder
        pub fn new() -> Self {
            let b = Sort::new("Bool".to_string(), 0);
            Builder {
                bool_: b.clone(),
                and_: Fun::new("and".to_string(), None, b.clone()),
                or_: Fun::new("or".to_string(), None, b.clone()),
                imply_: Fun::new("=>".to_string(), None, b.clone()),
                eq: Fun::new("and".to_string(), None, b.clone()),
                not_: Fun::new("and".to_string(), Some(vec![b.clone()]), b.clone()),
                vars: FxHashMap::default(),
                scopes: Vec::new(),
            }
        }
    }

    impl types::SortBuilder for Builder {
        type Sort = Sort;
        fn get_bool(&self) -> Sort { self.bool_.clone() }
        fn declare_sort(&mut self, s: &str, n: u8) -> Sort {
            Sort::new(s.to_string(),n)
        }
    }

    impl types::TermBuilder for Builder {
        type Fun = Fun;
        type Term = Term;

        fn get_builtin(&self, op: Op) -> Fun {
            match op {
                Op::And => self.and_.clone(),
                Op::Or => self.or_.clone(),
                Op::Imply => self.imply_.clone(),
                Op::Eq => self.eq.clone(),
                Op::Not => self.not_.clone(),
            }
        }

        fn declare_fun(&mut self, name: String, args: &[Sort], ret: Sort) -> Fun {
            let args = Some(args.iter().map(|s| s.clone()).collect());
            Fun::new(name, args, ret)
        }

        fn var(&mut self, s: &str) -> Option<Term> {
            self.vars.get(s).map(|t| t.clone())
        }

        fn ite(&mut self, a: Term, b: Term, c: Term) -> Term {
            Term::ite(a,b,c)
        }

        fn app_fun(&mut self, f: Fun, args: &[Term]) -> Term {
            Term::app_ref(f, args)
        }

        fn enter_let(&mut self, bs: &[(String,Term)]) {
            // save current bindings in `scopes`
            let scope =
                bs.iter()
                .map(|(s,_)| {
                    let old_t = self.vars.get(s).map(|t| t.clone());
                    let s = s.clone();
                    (s, old_t)
                })
                .collect();
            self.scopes.push(scope);
            for (s,t) in bs.iter() {
                self.vars.insert(s.clone(), t.clone());
            }
        }

        fn exit_let(&mut self, body: Term) -> Term {
            let scope = self.scopes.pop().expect("exit_let called too many times");
            for (s, old_t) in scope {
                // restore old binding for `s`, or remove it
                match old_t {
                    None => {
                        self.vars.remove(&s);
                    },
                    Some(t) => {
                        self.vars.insert(s,t);
                    },
                };
            }
            body
        }
    }
}

fn main() -> Result<(), Box<Error>> {
    env_logger::init();

    // TODO
    let mut _m = ast::Manager::new();
    let mut b = parse_ast::Builder::new();

    // parse
    let stmts = {
        let mut args = env::args();
        match args.skip(1).next() {
            None => {
                info!("parse stdin");
                parser::parse_stdin(&mut b)
            },
            Some(file) => {
                info!("parse file {:?}", file);
                let file = fs::File::open(file)?;
                parser::parse(&mut b, file)
            },
        }
    };

    println!("parsed statements {:?}", &stmts);

    Ok(())
}
