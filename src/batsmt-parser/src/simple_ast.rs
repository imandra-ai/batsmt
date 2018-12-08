
//! Simple representation of terms, sorts, etc.

use {
    fxhash::FxHashMap,
    std::{ops::Deref,rc::Rc, fmt, ptr},
    types::{self,Op},
    batsmt_pretty as pp,
};

// re-export
pub use batsmt_pretty::Pretty;

#[derive(Eq,PartialEq,Hash)]
struct SortCell {
    name: String,
    arity: u8,
}

/// A sort
#[derive(Clone,Eq,PartialEq,Hash)]
pub struct Sort(Rc<SortCell>);

impl fmt::Debug for Sort {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0.name, fmt)
    }
}

impl Sort {
    /// New sort
    fn new(name: String, arity: u8) -> Self {
        Sort(Rc::new(SortCell{name, arity}))
    }
}

#[derive(Eq,PartialEq,Hash)]
struct FunCell {
    name: String,
    args: Option<Vec<Sort>>,
    ret: Sort,
}

/// A function
#[derive(Clone,Eq,PartialEq,Hash)]
pub struct Fun(Rc<FunCell>);

impl Fun {
    /// New fun
    fn new(name: String, args: Option<Vec<Sort>>, ret: Sort) -> Self {
        Fun(Rc::new(FunCell {name, args, ret}))
    }
    pub fn ret(&self) -> Sort { self.0.ret.clone() }
    pub fn name(&self) -> &str { &self.0.name }
}

impl fmt::Debug for Fun {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0.name, fmt)
    }
}

/// The definition of a term node
pub enum TermCell {
    App(Fun, Vec<Term>),
    Ite(Term,Term,Term),
}

/// A term
#[derive(Clone)]
pub struct Term(Rc<TermCell>);

impl Eq for Term {}
impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        ptr::eq(&self.0, &other.0)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match &self.0.deref() {
            TermCell::Ite(a,b,c) => {
                write!(fmt, "(")?;
                fmt.debug_list().entries(&[a,b,c]).finish()?;
                write!(fmt, ")")
            },
            TermCell::App(f, args) => {
                if args.len () == 0 {
                    f.fmt(fmt)
                } else {
                    write!(fmt, "(")?;
                    fmt.debug_list().entry(f).entries(args.iter()).finish()?;
                    write!(fmt, ")")
                }
            },
        }
    }
}

impl Term {
    pub fn app(f: Fun, args: Vec<Term>) -> Self {
        Term(Rc::new(TermCell::App(f, args)))
    }
    pub fn app_ref(f: Fun, args: &[Term]) -> Self {
        let args = args.iter().map(|t| t.clone()).collect();
        Term::app(f, args)
    }
    pub fn ite(a: Term, b: Term, c: Term) -> Self {
        Term(Rc::new(TermCell::Ite(a,b,c)))
    }
}

/// The builder used for holding context and parsing
pub struct Builder {
    bool_: Sort,
    and_ : Fun,
    or_ : Fun,
    distinct : Fun,
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
            distinct: Fun::new("distinct".to_string(), None, b.clone()),
            not_: Fun::new("and".to_string(), Some(vec![b.clone()]), b.clone()),
            vars: FxHashMap::default(),
            scopes: Vec::new(),
        }
    }
}

impl types::SortBuilder for Builder {
    type Sort = Sort;
    fn get_bool(&self) -> Sort { self.bool_.clone() }
    fn declare_sort(&mut self, s: String, n: u8) -> Sort {
        Sort::new(s,n)
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
            Op::Distinct => self.distinct.clone(),
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

impl pp::Pretty for Sort {
    fn pp(&self, ctx: &mut pp::Ctx) {
        ctx.text(&self.0.name);
    }
}

impl pp::Pretty for Fun {
    fn pp(&self, ctx: &mut pp::Ctx) {
        ctx.text(&self.0.name);
    }
}

impl pp::Pretty for Term {
    fn pp(&self, ctx: &mut pp::Ctx) {
        match self.0.deref() {
            TermCell::Ite(a,b,c) => {
                ctx.sexp(|ctx| {
                    ctx.str("ite ").array(" ", &[a,b,c]);
                });
            },
            TermCell::App(f, args) => {
                if args.len() == 0 {
                    f.pp(ctx);
                } else {
                    ctx.sexp(|ctx| {
                        f.pp(ctx);
                        ctx.space().array(" ", args);
                    });
                }
            }
        }
    }
}

pretty_display!(Sort);
pretty_display!(Fun);
pretty_display!(Term);
