
use {
    batsmt_parser as parser,
    batsmt_pretty::{self as pp, Pretty1},
    batsmt_core::{ast_u32::AST, },
    crate::ctx::{Ctx, },
};

// print a statement by mapping its terms/sorts into `PP`
impl Pretty1<parser::Statement<AST,AST>> for Ctx {
    fn pp1_into(&self, st: &parser::Statement<AST,AST>, out: &mut pp::Ctx) {
        parser::pp_stmt(st, |ast,ctx| self.pp1_into(ast,ctx), |ast,ctx| self.pp1_into(ast,ctx), out)
    }
}
