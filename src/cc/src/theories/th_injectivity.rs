use {
    std::hash::Hash,
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, HashMap as BHMap}},
    crate::{
        cc::{self, MicroTheory, MicroTheoryArg, NodeID, },
        theories::SVec, 
        Ctx, pp_t, InjectiveView, HasInjectivity, },
};

/// State for the theory of injectivity.
pub struct Injectivity<F:Eq+Clone> {
    // TODO: bloom-filter of classes that have injective funs?
    /// `representative -> (f,t)+` where f: injective, `t=f(…)`
    /// There's at most one `(f,_)` per vector.
    repr: BHMap<NodeID, SVec<(F,AST)>>,
}

impl<C, F:Eq+Hash+Clone> Backtrackable<C> for Injectivity<F> {
    fn push_level(&mut self, _: &mut C) { self.repr.push_level() }
    fn pop_levels(&mut self, _: &mut C, n: usize) { self.repr.pop_levels(n) }
}

impl<F: Eq+Hash+Clone> Injectivity<F>
{
    #[inline]
    pub(crate) fn find_inj(&self, n: NodeID) -> Option<&SVec<(F,AST)>> {
        self.repr.get(&n)
    }
}

impl<C> MicroTheory<C> for Injectivity<<C as HasInjectivity<AST>>::F>
    where C: Ctx + HasInjectivity<AST>
{
    fn init(_m: &mut C) -> Self {
        Injectivity{ repr: BHMap::new() }
    }

    fn on_new_term(&mut self, c: &mut C, _: &mut cc::CC1<C>, t: &AST, n: NodeID) {
        match c.view_as_injective(t) {
            InjectiveView::AppInjective(f, _) => {
                // add to the table
                trace!("add {} to the injective entries for {:?}", pp_t(c,t), n);
                let v = SVec::from_elem((f.clone(),t.clone()),1);
                self.repr.insert(n, v);
            },
            InjectiveView::Other(..) => ()
        }
    }

    fn after_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, n1: NodeID, n2: NodeID) {
        // TODO: find a shortcut (per-node bitfield? bloom filter?)
        // to pre-filter whether n1 and n2 have at least one injective symbol

        if let Some(v1) = self.repr.get(&n1) {
            let mut v2_subset = SVec::new(); // to be added to v1

            if let Some(v2) = self.repr.get(&n2) {
                debug_assert!(v2.len()>0 && v1.len()>0);

                for (f2,t2) in v2.iter() {
                    match v1.iter().find(|(f1,t1)| f1 == f2 && t1 != t2) {
                        None => {
                            // will add to v1
                            v2_subset.push((f2.clone(),t2.clone()))
                        },
                        Some((_f1,t1)) => {
                            trace!("injectivity: merge arguments of {} and {}", pp_t(c,t1), pp_t(c,t2));

                            let n_t1 = acts.cc1.get_term_id(t1);
                            let n_t2 = acts.cc1.get_term_id(t2);

                            // explanation: `t1[i]=t2[i] <== t1=n1,n1=n2,n2=t2`
                            let expl = if n_t1 == n1 && n_t2 == n2 {
                                cc::Expl::AreEq(n1,n2)
                            } else {
                                let mut v = Vec::with_capacity(3);
                                v.push(cc::Expl::AreEq(n1,n2));
                                if n1 != n_t1 { v.push(cc::Expl::AreEq(n1,n_t1)) };
                                if n2 != n_t2 { v.push(cc::Expl::AreEq(n2,n_t2)) };
                                cc::Expl::Conj(v)
                            };

                            // merge arguments of `t1` and `t2` pairwise,
                            // since both are of the shape `f2(…)`
                            match (c.view_as_injective(t1), c.view_as_injective(t2)) {
                                (InjectiveView::AppInjective(f_t1, args1),
                                 InjectiveView::AppInjective(f_t2, args2)) => {
                                    assert_eq!(args1.len(), args2.len());
                                    debug_assert_eq!(f2, f_t1);
                                    debug_assert_eq!(f2, f_t2);

                                    for i in 0..args1.len() {
                                        let n_u1 = acts.cc1.get_term_id(&args1[i]);
                                        let n_u2 = acts.cc1.get_term_id(&args2[i]);
                                        acts.combine.push((n_u1, n_u2, expl.clone()))
                                    }
                                },
                                _ => unreachable!(),
                            }
                        }
                    }
                }
            }

            if v2_subset.len() > 0 {
                self.repr.update(&n1, |_, v1| {
                    // v1 <- v1 ++ v2
                    let v1 = v1.unwrap();
                    let mut v1_new = SVec::with_capacity(v1.len() + v2_subset.len());
                    v1_new.extend(v1.iter().cloned());
                    v1_new.extend(v2_subset.drain());
                    v1_new
                });
            }
        } else if let Some(v2) = self.repr.get(&n2) {
            // copy into v1
            self.repr.insert(n1, v2.clone());
        }
    }
}
