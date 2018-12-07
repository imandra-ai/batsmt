
pub trait SortBuilder {
    type Sort : Clone;

    fn get_bool(&self) -> Self::Sort;

    /// Declare a sort of the given arity
    fn declare_sort(&mut self, &str, u8) -> Self::Sort;
}

/// The builtins recognized by the parser
#[derive(Copy,Debug,Clone)]
pub enum Op { Or, And, Imply, Eq, Not }

pub trait TermBuilder : SortBuilder {
    type Fun : Clone;
    type Term : Clone;

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
    DeclareSort(u8),
    DeclareFun(String,Vec<Sort>,Sort),
    Assert(Term),
    CheckSat,
    Exit,
}

