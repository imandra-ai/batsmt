
//! Micro theories

use {
    std::hash::Hash,
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, HashMap as BHMap}},
    batsmt_pretty as pp,
    crate::{
        cc::{self, MicroTheory, MicroTheoryArg, NodeID, },
        Ctx, pp_t, IteView, InjectiveView, SelectorView,
        HasIte, HasInjectivity, HasDisjointness, HasSelector, },
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

/// A local small-vec
type SVec<T> = smallvec::SmallVec<[T; 4]>;

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
    fn find_inj(&self, n: NodeID) -> Option<&SVec<(F,AST)>> {
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

/// Theory of selectors on injective functions.
pub struct Selector<F:Eq+Clone> {
    inj: Injectivity<F>,
    sel: BHMap<NodeID, SVec<(F, AST)>>, // class -> parents that are selector-terms
}

impl<F:Eq+Clone> Selector<F> {
    /// Access the underlying theory of injectivity.
    pub fn injectivity(&self) -> &Injectivity<F> { &self.inj }
}

impl<C:Ctx, F:Eq+Hash+Clone> Backtrackable<C> for Selector<F> {
    fn push_level(&mut self, c: &mut C) {
        self.inj.push_level(c);
        self.sel.push_level();
    }
    fn pop_levels(&mut self, c: &mut C, n: usize) {
        self.inj.pop_levels(c, n);
        self.sel.pop_levels(n);
    }
}

impl<C> MicroTheory<C> for Selector<<C as HasInjectivity<AST>>::F>
    where C: Ctx + HasSelector<AST>
{
    fn init(m: &mut C) -> Self {
        Selector {
            inj: Injectivity::init(m),
            sel: BHMap::new(),
        }
    }

    fn on_new_term(&mut self, c: &mut C, cc1: &mut cc::CC1<C>, t: &AST, n: NodeID) {
        self.inj.on_new_term(c, cc1, t, n);

        match c.view_as_selector(t) {
            SelectorView::Select{f, idx: _, sub} => {
                // add to the set of selectors of `repr(sub)`
                let n_repr = cc1.find_t(sub);
                trace!("add {} to the selector entries for {:?}", pp_t(c,t), n_repr);
                let v = SVec::from_elem((f.clone(),t.clone()),1);
                self.sel.insert(n, v);
            },
            SelectorView::Other(..) => (),
        }
    }

    #[inline]
    fn on_sig_update(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, t: &AST, n: NodeID) {
        self.inj.on_sig_update(c, acts, t, n);
    }

    fn after_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, n1: NodeID, n2: NodeID) {
        self.inj.after_merge(c, acts, n1, n2);

        // merge the set of selector parents from both
        if let Some(v2) = self.sel.get(&n2) {
            let mut v2 = v2.clone();
            self.sel.update(&n1, move |_, v1_opt| {
                if let Some(v1) = v1_opt {
                    // append into `v2`
                    for x in v1.iter().cloned() { v2.push(x) };
                    v2
                } else {
                    v2
                }
            });
        }
    }

    fn before_merge(&mut self, c: &mut C, acts: &mut MicroTheoryArg<C>, a: NodeID, b: NodeID) {
        self.inj.before_merge(c, acts, a, b);

        let MicroTheoryArg{cc1, combine, ..} = acts;
        let mut pending_sel = SVec::new(); // selector parent terms

        // check parents of `a` of the shape `sel-f-idx(u)` with
        // terms of the class of `b` of the shape `f(…)`
        macro_rules! cross_prod {
            ($n1: expr, $n2: expr) => {
                if let Some(inj_2) = self.inj.find_inj($n2) {
                    if let Some(sel_1) = self.sel.get(&$n1) {
                        // cross product
                        for (f2,t2) in inj_2 {
                            for (f1,t1) in sel_1 {
                                if f1==f2 {
                                    pending_sel.push((t1, $n1, t2, $n2));
                                }
                            }
                        }
                    }
                }
            };
        }

        cross_prod!(a, b);
        cross_prod!(b, a);

        // `sel_t1 = select-f-idx(sub)` with `sub ~ n1`,
        // `inj_t2 = f(u2_1… u2_n)` with `inj_t2 ~ n2`
        //
        // let's merge `sel_t1` with `u2_idx`
        for (sel_t1, n1, inj_t2, n2) in pending_sel {

            let (f, idx, sub) = match c.view_as_selector(sel_t1) {
                SelectorView::Select{f, idx, sub} => { (f.clone(), idx, sub) },
                SelectorView::Other(..) => unreachable!(),
            };

            let n_sub = cc1.get_term_id(sub);
            debug_assert_eq!(cc1.find(n_sub), n1);

            let inj_t2_idx = match c.view_as_injective(inj_t2) {
                InjectiveView::AppInjective(f2, args) => {
                    debug_assert_eq!(f, *f2);
                    args[idx as usize]
                },
                InjectiveView::Other(..) => unreachable!(),
            };

            trace!("selector: merge {} and {}", pp_t(c, &inj_t2_idx), pp_t(c,sel_t1));

            {
                // expl: either `n_sub==(n2 := f(t1…tn)) => select-f-i(n_sub) == ti`
                // or `select-f-i(f(t1…tn)) = ti` by axiom
                let expl = if n_sub == n2 {
                    cc::Expl::Axiom
                } else {
                    cc::Expl::AreEq(n_sub, n2)
                };
                let n_sel_t1 = cc1.get_term_id(sel_t1);
                let n_inj_t2_idx = cc1.get_term_id(&inj_t2_idx);
                combine.push((n_sel_t1, n_inj_t2_idx, expl));
            }
        }
    }
}
