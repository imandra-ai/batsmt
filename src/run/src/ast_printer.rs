
use {
    batsmt_parser as parser,
    batsmt_pretty::{self as pretty, Pretty},
    batsmt_core::{ast,AST,Symbol,StrSymbol},
    std::fmt,
};

/// A pretty-printable version of a `T` that contains ASTs
#[derive(Clone)]
pub struct PP<S:Symbol,T>(ast::Manager<S>, T);

impl<S:Symbol,T> PP<S,T> {
    /// Wrap the given AST (with its manager) into a pretty-printable version
    pub fn new(m: &ast::Manager<S>, x: T) -> Self { PP(m.clone(), x) }
}

// how to pretty-print an AST
impl Pretty for PP<StrSymbol,AST> {
    fn pp(&self, ctx: &mut pretty::Ctx) {
        let m = self.0.clone();
        let r = m.get();
        match r.view(self.1) {
            ast::View::Const(s) => {
                s.pp(ctx);
            },
            ast::View::App{f, args} if args.len() == 0 => {
                let f = PP::new(&m,f);
                f.pp(ctx);
            },
            ast::View::App{f, args} => {
                let m = m.clone();
                ctx.sexp(move |mut ctx| {
                    let f = PP::new(&m,f);
                    f.pp(&mut ctx);
                    ctx.space()
                        .iter(" ", args.iter().map(move |a| PP::new(&m,*a)));
                });
            }
        }
    }
}

// print a statement by mapping its terms/sorts into `PP`
impl Pretty for PP<StrSymbol, parser::Statement<AST,AST>> {
    fn pp(&self, out: &mut pretty::Ctx) {
        let m = &self.0;
        let st = self.1.clone();
        let st = st.map(|ast| PP::new(m, ast), |ast| PP::new(m,ast));
        st.pp(out)
    }
}

impl<S:Symbol,T> fmt::Display for PP<S,T> where Self : Pretty {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.pp_fmt(out)
    }
}
