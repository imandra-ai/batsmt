
use {
    batsmt_parser as parser,
    batsmt_pretty::{self as pretty, Pretty},
    batsmt_core::{ast::{Manager, View}, ast_u32::AST,},
    crate::ctx::{Ctx, },
    std::fmt,
};

/// A pretty-printable version of a `T` that contains ASTs
#[derive(Clone)]
pub struct PP<'a, T>(&'a Ctx, T);

impl<'a,T> PP<'a,T> {
    /// Wrap the given AST (with its manager) into a pretty-printable version
    pub fn new(m: &'a Ctx, x: T) -> Self { PP(m, x) }
}

// how to pretty-print an AST
impl<'a> Pretty for PP<'a,AST> {
    fn pp_into(&self, ctx: &mut pretty::Ctx) {
        let m = self.0;
        match m.view(&self.1) {
            View::Const(s) => {
                s.pp_into(ctx);
            },
            View::App{f, args} if args.len() == 0 => {
                let f = PP::new(&m,f);
                f.pp_into(ctx);
            },
            View::App{f, args} => {
                let m = m.clone();
                ctx.sexp(move |mut ctx| {
                    let f = PP::new(&m,f);
                    f.pp_into(&mut ctx);
                    ctx.space()
                        .iter(" ", args.iter().map(move |a| PP::new(&m,*a)));
                });
            }
        }
    }
}

// print a statement by mapping its terms/sorts into `PP`
impl<'a> Pretty for PP<'a, parser::Statement<AST,AST>> {
    fn pp_into(&self, out: &mut pretty::Ctx) {
        let m = &self.0;
        let st = self.1.clone();
        let st = st.map(|ast| PP::new(m, ast), |ast| PP::new(m,ast));
        st.pp_into(out)
    }
}

impl<'a,T> fmt::Display for PP<'a,T> where Self : Pretty {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.pp_fmt(out,false)
    }
}
