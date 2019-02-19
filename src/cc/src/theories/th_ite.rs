
use {
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, }},
    crate::{
        cc::{self, MicroTheory, MicroTheoryArg, NodeID, },
        Ctx, IteView, HasIte, },
};

/// Theory of `if then else`.
pub struct Ite;

impl<C> Backtrackable<C> for Ite {
    fn push_level(&mut self, _: &mut C) {}
    fn pop_levels(&mut self, _: &mut C, _: usize) {}
}

impl<C> MicroTheory<C> for Ite where C: Ctx + HasIte<AST> {
    fn init(_m: &mut C) -> Self { Ite }

    fn on_sig_update(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, t: &AST, n_t: NodeID)
    {
        match c.view_as_ite(t) {
            IteView::Ite(a,b,c) => {
                let MicroTheoryArg{n_true,n_false,cc1,combine,..} = acts;
                let a = cc1.get_term_id(a);
                let b = cc1.get_term_id(b);
                let c = cc1.get_term_id(c);
                if cc1.is_eq(a, *n_true) {
                    // a=true => if(a,b,c)=b
                    combine.push((n_t, b, cc::Expl::AreEq(a, *n_true)));
                } else if cc1.is_eq(a, *n_false) {
                    // a=false => if(a,b,c)=c
                    combine.push((n_t, c, cc::Expl::AreEq(a, *n_false)));
                } else if cc1.is_eq(b,c) {
                    // b=c => if(a,b,c)=b
                    combine.push((n_t, b, cc::Expl::AreEq(b, c)));
                }
            },
            IteView::Other(..) => ()
        }
    }
}
