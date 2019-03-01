
//! A mix of injectivity and disjointness, without selectors

use {
    std::hash::Hash,
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, HashMap as BHMap}},
    batsmt_pretty as pp,
    crate::{
        cc::{self, MicroTheory, MicroTheoryArg, NodeID, },
        Ctx, pp_t, ConstructorView as CView, HasConstructor,
    },
};

#[derive(Clone,Eq,PartialEq)]
struct ReprState<F: Eq+Clone> {
    cstor: (F,AST),
}

/// State for the theory of constructors.
pub struct Constructor<F:Eq+Clone> {
    // TODO: bloom-filter of classes that have injective funs?
    /// `representative -> (f,t)?` where f: injective, `t=f(…)`
    /// There's at most one `(f,_)` per node.
    repr: BHMap<NodeID, ReprState<F>>,
}

impl<C, F:Eq+Hash+Clone> Backtrackable<C> for Constructor<F> {
    fn push_level(&mut self, _: &mut C) { self.repr.push_level() }
    fn pop_levels(&mut self, _: &mut C, n: usize) { self.repr.pop_levels(n) }
}

impl<C> MicroTheory<C> for Constructor<<C as HasConstructor<AST>>::F>
    where C: Ctx + HasConstructor<AST>
{
    fn init(_m: &mut C) -> Self {
        Constructor{ repr: BHMap::new() }
    }

    fn on_new_term(&mut self, c: &mut C, cc1: &mut cc::CC1<C>, t: &AST, n: NodeID) {
        match c.view_as_constructor(t) {
            CView::AppConstructor(f, _) => {
                // add to the table
                trace!("add {} to the constructor entries for {:?}", pp_t(c,t), n);
                let st = ReprState {
                    cstor: (f.clone(),t.clone()),
                };
                debug_assert_eq!(n, cc1.find(n));
                self.repr.insert(n, st);
            },
            CView::Other(..) => ()
        }
    }

    fn after_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, n1: NodeID, n2: NodeID) {
        // TODO: find a shortcut (per-node bitfield? bloom filter?)
        // to pre-filter whether n1 and n2 have at least one injective symbol

        if let Some(ref st2) = self.repr.get(&n2) {
            if let Some(ref st1) = self.repr.get(&n1) {
                let (f1,t1) = &st1.cstor;
                let (f2,t2) = &st2.cstor;
                if f1 == f2 {
                    // merge args pairwise
                    let n_t1 = acts.cc1.get_term_id(&t1);
                    let n_t2 = acts.cc1.get_term_id(&t2);

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
                    match (c.view_as_constructor(&t1), c.view_as_constructor(&t2)) {
                        (CView::AppConstructor(f_t1, args1),
                        CView::AppConstructor(f_t2, args2)) => {
                            assert_eq!(args1.len(), args2.len());
                            debug_assert_eq!(*f2, *f_t1);
                            debug_assert_eq!(*f2, *f_t2);

                            for i in 0..args1.len() {
                                let n_u1 = acts.cc1.get_term_id(&args1[i]);
                                let n_u2 = acts.cc1.get_term_id(&args2[i]);

                                trace!("injectivity: merge {} and {} (sub-{} of {} and {})",
                                    pp::pp2(acts.cc1,c,&n_u1), pp::pp2(acts.cc1,c,&n_u2),
                                    i, pp_t(c,t1), pp_t(c,t2));

                                acts.combine.push((n_u1, n_u2, expl.clone()))
                            }
                        },
                        _ => unreachable!(),
                    };
                } else {
                    // conflict
                    let MicroTheoryArg{cc1,n_true,n_false,combine,..} = acts;
                    trace!("disjointness: failure for {} (= {}) and {} (= {})",
                           pp::pp2(*cc1,c,&n1), pp_t(c,t1), pp::pp2(*cc1,c,&n2), pp_t(c,t2));
                    // conflict by `false <== n1=n2 & n1=t1 & n2=t2`
                    let n_t1 = cc1.get_term_id(&t1);
                    let n_t2 = cc1.get_term_id(&t2);
                    let expl = if n_t1 == n1 && n_t2 == n2 {
                        cc::Expl::AreEq(n1,n2)
                    } else {
                        let mut v = Vec::with_capacity(3);
                        v.push(cc::Expl::AreEq(n1,n2));
                        if n1 != n_t1 { v.push(cc::Expl::AreEq(n1, n_t1)) };
                        if n2 != n_t2 { v.push(cc::Expl::AreEq(n2, n_t2)) };
                        cc::Expl::Conj(v)
                    };
                    combine.push((*n_true, *n_false, expl));
                    return
                };

                // t1 and t2 are equal, just keep t1
            } else {
                // copy into v1
                self.repr.insert(n1, (*st2).clone());
            }
        }
    }
}
