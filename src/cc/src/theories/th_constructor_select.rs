
//! A mix of selector, injectivity, and disjointness

use {
    std::hash::Hash,
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, HashMap as BHMap}},
    batsmt_pretty as pp,
    crate::{
        cc::{self, MicroTheory, MicroTheoryArg, NodeID, },
        theories::SVec,
        Ctx, pp_t, ConstructorSelectView as CView, HasConstructorSelect,
    },
};

#[derive(Clone,Eq,PartialEq)]
struct ReprState<F: Eq+Clone> {
    sel: SVec<(F,AST)>,
    cstor: Option<(F,AST)>,
}

/// State for the theory of constructors + select
pub struct ConstructorSelect<F:Eq+Clone> {
    // TODO: bloom-filter of classes that have injective funs?
    /// `representative -> (f,t)?` where f: injective, `t=f(…)`
    /// There's at most one `(f,_)` per node.
    repr: BHMap<NodeID, ReprState<F>>,
}

impl<C, F:Eq+Hash+Clone> Backtrackable<C> for ConstructorSelect<F> {
    fn push_level(&mut self, _: &mut C) { self.repr.push_level() }
    fn pop_levels(&mut self, _: &mut C, n: usize) { self.repr.pop_levels(n) }
}

impl<F: Eq+Hash+Clone> ConstructorSelect<F> {
    #[inline]
    fn find_st(&self, n: NodeID) -> Option<&ReprState<F>> {
        self.repr.get(&n)
    }
}

impl<C> MicroTheory<C> for ConstructorSelect<<C as HasConstructorSelect<AST>>::F>
    where C: Ctx + HasConstructorSelect<AST>
{
    fn init(_m: &mut C) -> Self {
        ConstructorSelect{ repr: BHMap::new() }
    }

    fn on_new_term(&mut self, c: &mut C, cc1: &mut cc::CC1<C>, t: &AST, n: NodeID) {
        match c.view_as_constructor_select(t) {
            CView::AppConstructor(f, _) => {
                // add to the table
                trace!("add {} to the constructor entries for {:?}", pp_t(c,t), n);
                let st = ReprState {
                    sel: SVec::new(),
                    cstor: Some((f.clone(),t.clone())),
                };
                debug_assert_eq!(n, cc1.find(n));
                self.repr.insert(n, st);
            },
            CView::Select {f, idx:_, sub} => {
                // add to the set of selectors of `repr(sub)`
                let n_repr = cc1.find_t(sub);
                trace!("add {} to the selector entries for {:?}", pp_t(c,t), n_repr);
                self.repr.update(&n_repr, |_, st_opt| {
                    match st_opt {
                        Some(st) => {
                            let mut st = st.clone();
                            st.sel.push((f.clone(), t.clone()));
                            st
                        },
                        None => {
                            ReprState {
                                sel: SVec::from_elem((f.clone(),t.clone()), 1),
                                cstor: None,
                            }
                        },
                    }
                });
            },
            CView::Other(..) => ()
        }
    }

    fn before_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, a: NodeID, b: NodeID) {
        let MicroTheoryArg{cc1, combine, ..} = acts;
        let mut pending_sel = SVec::new(); // selector parent terms

        // check parents of `n1` of the shape `sel-f-idx(u)` with
        // terms of the class of `n2` of the shape `f(…)`
        macro_rules! cross_prod {
            ($n1: expr, $n2: expr) => {
                if let Some(ReprState {cstor:Some((f2,t2)), ..}) = self.find_st($n2) {
                    if let Some(st_1) = self.find_st($n1) {
                        // cross product
                        for (f1,t1) in st_1.sel.iter() {
                            if *f1 == *f2 {
                                pending_sel.push((t1.clone(), $n1, t2.clone(), $n2));
                            }
                        }
                    }
                };
            };
        }

        cross_prod!(a, b);
        cross_prod!(b, a);

        // `sel_t1 = select-f-idx(sub)` with `sub ~ n1`,
        // `inj_t2 = f(u2_1… u2_n)` with `inj_t2 ~ n2`
        //
        // let's merge `sel_t1` with `u2_idx`
        for (sel_t1, n1, inj_t2, n2) in pending_sel {

            let (f, idx, sub) = match c.view_as_constructor_select(&sel_t1) {
                CView::Select{f, idx, sub} => { (f.clone(), idx, sub) },
                _ => unreachable!(),
            };

            let n_sub = cc1.get_term_id(sub);
            debug_assert_eq!(cc1.find(n_sub), n1);

            let inj_t2_idx = match c.view_as_constructor_select(&inj_t2) {
                CView::AppConstructor(f2, args) => {
                    debug_assert_eq!(f, *f2);
                    args[idx as usize]
                },
                _ => unreachable!(),
            };

            trace!("selector: merge {} and {}", pp_t(c, &inj_t2_idx), pp_t(c,&sel_t1));

            {
                // expl: either `n_sub==(n2 := f(t1…tn)) => select-f-i(n_sub) == ti`
                // or `select-f-i(f(t1…tn)) = ti` by axiom
                let expl = if n_sub == n2 {
                    cc::Expl::Axiom
                } else {
                    cc::Expl::AreEq(n_sub, n2)
                };
                let n_sel_t1 = cc1.get_term_id(&sel_t1);
                let n_inj_t2_idx = cc1.get_term_id(&inj_t2_idx);
                combine.push((n_sel_t1, n_inj_t2_idx, expl));
            }
        }
    }

    fn after_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, n1: NodeID, n2: NodeID) {
        // TODO: find a shortcut (per-node bitfield? bloom filter?)
        // to pre-filter whether n1 and n2 have at least one injective symbol

        if let Some(ref st2) = self.repr.get(&n2) {
            if let Some(ref st1) = self.repr.get(&n1) {
                let new_cstor_opt = match (&st1.cstor, &st2.cstor) {
                    (Some((f1,t1)), Some ((f2,t2))) => {
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
                            match (c.view_as_constructor_select(&t1),
                                    c.view_as_constructor_select(&t2)) {
                                (CView::AppConstructor(f_t1, args1),
                                CView::AppConstructor(f_t2, args2)) => {
                                    assert_eq!(args1.len(), args2.len());
                                    debug_assert_eq!(*f2, *f_t1);
                                    debug_assert_eq!(*f2, *f_t2);

                                    for i in 0..args1.len() {
                                        let n_u1 = acts.cc1.get_term_id(&args1[i]);
                                        let n_u2 = acts.cc1.get_term_id(&args2[i]);
                                        acts.combine.push((n_u1, n_u2, expl.clone()))
                                    }
                                },
                                _ => unreachable!(),
                            };

                            // t1 and t2 are equal, just keep t1
                            None
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
                        }
                    },
                    (Some(..), None) => None,
                    (None, Some(tup)) => Some(tup.clone()),
                    (None, None) => None,
                };

                // update `st1`
                if new_cstor_opt.is_some() || st2.sel.len() > 0 {
                    let st2_sel = st2.sel.clone();
                    drop(st1);
                    drop(st2);

                    self.repr.update(&n1, move |_,v1_opt| {
                        let mut s = v1_opt.unwrap().clone();
                        s.sel.extend(st2_sel.iter().cloned());
                        if let Some(new_cstor) = new_cstor_opt {
                            s.cstor = Some(new_cstor);
                        }
                        s
                    });
                }
            } else {
                // copy into v1
                self.repr.insert(n1, (*st2).clone());
            }
        }
    }
}
