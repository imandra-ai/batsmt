
use {
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, HashMap as BHMap}},
    batsmt_pretty as pp,
    crate::{
        cc::{self, MicroTheory, MicroTheoryArg, NodeID, },
        Ctx, pp_t, HasDisjointness, },
};

/// Theory of disjoint labels (e.g constructors or finite domain elements).
pub struct Disjointness<F:Clone+Eq> {
    label: BHMap<NodeID, (F, AST)>, // label of the class, if any
}

impl<C, F:Eq+Clone> Backtrackable<C> for Disjointness<F> {
    fn push_level(&mut self, _: &mut C) { self.label.push_level() }
    fn pop_levels(&mut self, _: &mut C, n: usize) { self.label.pop_levels(n) }
}

impl<C> MicroTheory<C> for Disjointness<<C as HasDisjointness<AST>>::F>
    where C: Ctx + HasDisjointness<AST>
{
    fn init(_m: &mut C) -> Self {
        Disjointness{ label: BHMap::new() }
    }

    fn on_new_term(&mut self, c: &mut C, _: &mut cc::CC1<C>, t: &AST, n: NodeID) {
        match c.get_disjoint_label(t) {
            Some(f) => {
                // add to the table
                trace!("add disjoint label to {}", pp_t(c,t));
                self.label.insert(n, (f,t.clone()));
            },
            None => (),
        }
    }

    fn after_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, n1: NodeID, n2: NodeID) {
        // TODO: find a shortcut (per-node bitfield? bloom filter?)
        // to pre-filter whether n1 and n2 have a label

        if let Some((f2,t2)) = self.label.get(&n2) {
            if let Some((f1,t1)) = self.label.get(&n1) {
                if f1 != f2 {
                    let MicroTheoryArg{cc1,n_true,n_false,combine,..} = acts;
                    trace!("disjointness: failure for {} and {}",
                           pp::pp2(*cc1,c,&n1), pp::pp2(*cc1,c,&n2));
                    // conflict by `false <== n1=n2 & n1=t1 & n2=t2`
                    let n_t1 = cc1.get_term_id(t1);
                    let n_t2 = cc1.get_term_id(t2);
                    let expl = if n_t1 == n1 && n_t2 == n2 {
                        cc::Expl::AreEq(n1,n2)
                    } else {
                        let mut v = Vec::with_capacity(3);
                        v.push(cc::Expl::AreEq(n1,n2));
                        if n1 != n_t1 { v.push(cc::Expl::AreEq(n1, n_t1)) };
                        if n2 != n_t2 { v.push(cc::Expl::AreEq(n2, n_t2)) };
                        cc::Expl::Conj(v)
                    };
                    combine.push((*n_true, *n_false, expl))
                }
            } else {
                // copy label into n1
                self.label.insert(n1, (f2.clone(), t2.clone()));
            }
        }
    }
}
