
//! Micro theories

use {
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, HashMap as BHMap}},
    crate::{
        cc::{self, MicroTheory, NodeID, },
        Ctx, IteView, HasIte, InjectiveView, HasInjectivity, },
};

pub struct Ite;

impl<C> Backtrackable<C> for Ite {
    fn push_level(&mut self, _: &mut C) {}
    fn pop_levels(&mut self, _: &mut C, _: usize) {}
}

impl<C> MicroTheory<C> for Ite where C: Ctx + HasIte<AST> {
    fn init(_m: &mut C) -> Self { Ite }

    #[inline]
    fn on_merge(&mut self, _c: &mut C, _acts: &mut cc::MergePhase<C>, _n1: NodeID, _n2: NodeID) {}

    // TODO: if then=else, also merge with then
    fn on_signature(&mut self, c: &mut C, acts: &mut cc::UpdateSigPhase<C>, t: &AST) {
        match c.view_as_ite(t) {
            IteView::Ite(a,b,c) => {
                let cc::UpdateSigPhase{n_true,n_false,cc1,combine,..} = acts;
                let a = cc1.get_term_id(a);
                let b = cc1.get_term_id(b);
                let c = cc1.get_term_id(c);
                if cc1.is_eq(a, *n_true) {
                    // a=true => if(a,b,c)=b
                    let t = cc1.get_term_id(t);
                    combine.push((t, b, cc::Expl::AreEq(a, *n_true)));
                } else if cc1.is_eq(a, *n_false) {
                    // a=false => if(a,b,c)=c
                    let t = cc1.get_term_id(t);
                    combine.push((t, c, cc::Expl::AreEq(a, *n_false)));
                } else if cc1.is_eq(b,c) {
                    // b=c => if(a,b,c)=b
                    let t = cc1.get_term_id(t);
                    combine.push((t, b, cc::Expl::AreEq(b, c)));
                }
            },
            IteView::Other(..) => ()
        }
    }
}

/* TODO
pub struct Injectivity<F:Eq+Hash> {
    repr: BHMap<(NodeID,F), AST>, // (root,injective-fun) => a term in the class with this function
}

pub struct Disjointness<F:Clone> {
    label: BHMap<NodeID, F>, // label of the class, if any
}

pub struct Selector;

impl<C, F> MicroTheory<C> for Injectivity
    where F: Eq,
          C: Ctx + HasInjectivity<F, AST>
{
    // TODO: store one term per injective function per class
    type State = ();

    fn init(_m: &mut C) -> Self { Injectivity }

    fn on_merge(&mut self, c: &mut C, acts: &mut cc::MergePhase<C>, n1: NodeID, n2: NodeID) {
        let t1 = acts.cc1[n1].ast;
        let t2 = acts.cc1[n2].ast;
        match c.view(t) {


        }
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

    #[inline]
    fn on_signature(&mut self, _c: &mut C, _acts: &mut cc::UpdateSigPhase<C>, _t: &AST) {}
}
*/
