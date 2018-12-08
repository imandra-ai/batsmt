
use std::fmt::{self,Debug};
use batsmt_pretty as pp;
pub use self::pp::Pretty;

pub trait SortBuilder {
    type Sort : Clone + Debug;

    fn get_bool(&self) -> Self::Sort;

    /// Declare a sort of the given arity
    fn declare_sort(&mut self, String, u8) -> Self::Sort;
}

/// The builtins recognized by the parser
#[derive(Copy,Debug,Clone)]
pub enum Op { Or, And, Imply, Eq, Not, Distinct }

pub trait TermBuilder : SortBuilder {
    type Fun : Clone + Debug;
    type Term : Clone + Debug;

    /// Builtins

    fn get_builtin(&self, op: Op) -> Self::Fun;

    /// Term from a bound variable
    fn var(&mut self, &str) -> Option<Self::Term>;

    /// Declare a function
    fn declare_fun(&mut self, name: String, &[Self::Sort], Self::Sort) -> Self::Fun;

    /// Build a term by function application
    fn app_fun(&mut self, Self::Fun, &[Self::Term]) -> Self::Term;

    /// Build a `ite` term
    fn ite(&mut self, Self::Term, Self::Term, Self::Term) -> Self::Term;

    /// Build a let binding. The variables may be called from now on.
    fn enter_let(&mut self, &[(String, Self::Term)]);

    fn exit_let(&mut self, body: Self::Term) -> Self::Term;
}


/// A toplevel statement
#[derive(Debug,Clone)]
pub enum Statement<Term, Sort> {
    SetInfo(String,String),
    SetLogic(String),
    DeclareSort(String,u8),
    DeclareFun(String,Vec<Sort>,Sort),
    Assert(Term),
    CheckSat,
    Exit,
}


impl<T,S> pp::Pretty for Statement<T,S>
    where T: pp::Pretty, S: pp::Pretty
{
    fn pp(&self, ctx: &mut pp::Ctx) {
        match self {
            &Statement::SetInfo(ref a, ref b) => {
                ctx.sexp(|ctx| {
                    ctx.str("set-info").space().pp(&a).space().pp(&b);
                });
            },
            &Statement::SetLogic(ref a) => {
                ctx.sexp(|ctx| {
                    ctx.str("set-logic").space().pp(&a);
                });
            },
            &Statement::DeclareSort(ref s,n) => {
                ctx.sexp(|ctx| {
                    ctx.str("declare-sort").space().pp(&s).space().text_string(n.to_string());
                });
            },
            &Statement::DeclareFun(ref f, ref args, ref ret) => {
                ctx.sexp(|ctx| {
                    ctx.str("declare-fun").space().pp(&f).
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
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result { Pretty::pp_fmt(&self,out) }
}

#[test]
fn test_pp() {
    use simple_ast as a;
    let st: Statement<a::Term, a::Sort> = Statement::Exit;
    let s = format!("{}", &st);
    assert_eq!("(exit)", s);
}
