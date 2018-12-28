
use {
    std::{fmt::{self,Debug}, rc::Rc},
    batsmt_pretty as pp,
};
pub use self::pp::Pretty;

/// An atom is a refcounted string
pub type Atom = Rc<str>;

pub trait SortBuilder {
    type Sort : Clone + Debug;

    fn get_bool(&self) -> Self::Sort;

    /// Declare a sort of the given arity
    fn declare_sort(&mut self, name: Atom, arity: u8) -> Self::Sort;
}

/// The builtins recognized by the parser
#[derive(Copy,Debug,Clone)]
pub enum Op { True, False, Or, And, Imply, Eq, Not, Distinct }

pub trait TermBuilder : SortBuilder {
    type Fun : Clone + Debug;
    type Term : Clone + Debug;
    type Var : Clone + Debug; // bound variable

    /// Builtins

    fn get_builtin(&self, op: Op) -> Self::Fun;

    /// Term from a bound variable
    fn var(&mut self, v: Self::Var) -> Self::Term;

    /// Declare a function
    fn declare_fun(&mut self, name: Atom, args: &[Self::Sort], ret: Self::Sort) -> Self::Fun;

    /// Build a term by function application
    fn app_fun(&mut self, f: Self::Fun, args: &[Self::Term]) -> Self::Term;

    /// Build a `ite` term
    fn ite(&mut self, _: Self::Term, _: Self::Term, _: Self::Term) -> Self::Term;

    /// Make a variable bound to this term
    fn bind(&mut self, name: Atom, t: Self::Term) -> Self::Var;

    /// Build a let binding. The variables may be called from now on.
    fn let_(&mut self, bs: &[(Self::Var, Self::Term)], body: Self::Term) -> Self::Term;
}


/// A toplevel statement
#[derive(Debug,Clone)]
pub enum Statement<Term, Sort> {
    SetInfo(Atom,Atom),
    SetLogic(Atom),
    DeclareSort(Atom,u8),
    DeclareFun(Atom,Vec<Sort>,Sort),
    Assert(Term),
    CheckSat,
    Exit,
}

impl<T,S> Statement<T,S> {
    /// Tranform terms and sorts
    pub fn map<T2,S2,FT,FS>(self, mut ft: FT, mut fs: FS) -> Statement<T2,S2>
        where FT: FnMut(T)->T2, FS: FnMut(S) -> S2
    {
        use super::Statement::*;
        match self {
            SetInfo(a,b) => SetInfo(a,b),
            SetLogic(a) => SetLogic(a),
            DeclareSort(s,n) => DeclareSort(s,n),
            DeclareFun(s,args,ret) => {
                let args = args.into_iter().map(|s| fs(s)).collect();
                let ret = fs(ret);
                DeclareFun(s,args,ret)
            },
            Assert(t) => Assert(ft(t)),
            CheckSat => CheckSat,
            Exit => Exit,
        }
    }
}

impl<T,S> pp::Pretty for Statement<T,S>
    where T: pp::Pretty, S: pp::Pretty
{
    fn pp_into(&self, ctx: &mut pp::Ctx) {
        match self {
            &Statement::SetInfo(ref a, ref b) => {
                ctx.sexp(|ctx| {
                    ctx.str("set-info").space().pp(&a).space().pp(&pp::dbg(&b));
                });
            },
            &Statement::SetLogic(ref a) => {
                ctx.sexp(|ctx| {
                    ctx.str("set-logic").space().pp(&a);
                });
            },
            &Statement::DeclareSort(ref s,n) => {
                ctx.sexp(|ctx| {
                    ctx.str("declare-sort").space().pp(&s).space().string(n.to_string());
                });
            },
            &Statement::DeclareFun(ref f, ref args, ref ret) => {
                ctx.sexp(|ctx| {
                    ctx.str("declare-fun").space().pp(&f).space().
                        sexp(|ctx| { ctx.array(pp::space(), &args); }).space().pp(&ret);
                });
            },
            &Statement::Assert(ref t) => {
                ctx.sexp(|ctx| {
                    ctx.str("assert").space().pp(&t);
                });
            },
            &Statement::CheckSat => { ctx.str("(check-sat)"); },
            &Statement::Exit => { ctx.str("(exit)"); },
        }
    }
}

impl<T:Pretty,S:Pretty> fmt::Display for Statement<T,S> {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result { Pretty::pp_fmt(&self,out,true) }
}

#[test]
fn test_pp() {
    use crate::simple_ast as a;
    let st: Statement<a::Term, a::Sort> = Statement::Exit;
    let s = format!("{}", &st);
    assert_eq!("(exit)", s);
}
