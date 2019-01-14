
use {
    batsmt_parser as parser,
    batsmt_pretty::{self as pp, Pretty, Pretty1},
    batsmt_core::{ast::{Manager, View}, ast_u32::AST,},
    crate::ctx::{Ctx, },
    std::fmt,
};

// how to pretty-print an AST
impl Pretty1<AST> for Ctx {
    fn pp1_into(&self, t: &AST, ctx: &mut pp::Ctx) {
        let m = self;
        match m.view(t) {
            View::Const(s) => {
                s.pp_into(ctx);
            },
            View::App{f, args} if args.len() == 0 => {
                ctx.pp1(self, f);
            },
            View::App{f, args} => {
                let m = m.clone();
                ctx.sexp(move |mut ctx| {
                    ctx.pp1(self, f);
                    ctx.space()
                        .iter(" ", args.iter().map(move |a| pp::pp1(self, a)));
                });
            }
        }
    }
}

// print a statement by mapping its terms/sorts into `PP`
impl Pretty1<parser::Statement<AST,AST>> for Ctx {
    fn pp1_into(&self, st: &Statement<AST<AST>, out: &mut pp::Ctx) {
        let st = st.clone();
        let st = st.map(|ast| pp::pp1(m, ast), |ast| pp::pp1(m,ast));
        st.pp_into(out)
    }
}
