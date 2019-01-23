
//! Micro theories

use {
    batsmt_core::ast_u32::AST,
    crate::{
        cc::{self, MicroTheory, MicroTheoryState, NodeID, },
        IteView, HasIte, Ctx, },
};

pub struct Ite;
pub struct IteState;

impl<C> MicroTheoryState<C> for IteState where C: Ctx + HasIte<AST> {
    fn init(m: &mut C, t: &C::AST) -> Self { IteState }
    fn merge(&mut self, other: &Self) { }
    fn unmerge(&mut self, other: &Self) { }
}

impl<C> MicroTheory<C> for Ite where C: Ctx + HasIte<AST> {
    type State = IteState;

    fn init(_m: &mut C) -> Self { Ite }

    #[inline]
    fn on_merge(&mut self, _c: &mut C, _acts: &mut cc::MergePhase<C>, _n1: NodeID, _n2: NodeID) {
    }

    fn on_signature(&mut self, c: &mut C, acts: &mut cc::UpdateSigPhase<C>, t: &AST) {
        match c.view_as_ite(t) {
            IteView::Ite(a,b,c) => {
                let cc::UpdateSigPhase{n_true,n_false,cc1,combine,..} = acts;
                let a = cc1.get_term_id(a);
                if cc1.is_eq(a, *n_true) {
                    let t = cc1.get_term_id(t);
                    let b = cc1.get_term_id(b);
                    combine.push((t, b, cc::Expl::AreEq(a, *n_true)));
                } else if cc1.is_eq(a, *n_false) {
                    let t = cc1.get_term_id(t);
                    let c = cc1.get_term_id(c);
                    combine.push((t, c, cc::Expl::AreEq(a, *n_false)));
                }
            },
            IteView::Other(..) => ()
        }
    }
}

