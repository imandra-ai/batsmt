

use {
    std::hash::Hash,
    batsmt_core::{ast_u32::AST, backtrack::{Backtrackable, HashMap as BHMap}},
    crate::{
        cc::{self, MicroTheory, MicroTheoryArg, NodeID, },
        theories::{SVec,Injectivity},
        Ctx, pp_t, InjectiveView, SelectorView,
        HasInjectivity, HasSelector, },
};

/// Theory of selectors on injective functions.
pub struct Selector<F:Eq+Clone> {
    inj: Injectivity<F>,
    sel: BHMap<NodeID, SVec<(F, AST)>>, // class -> parents that are selector-terms
}

/// An underlying provider of injective symbols we can select over.
pub trait HasInjective<F:Eq+Clone> {
    /// For the given representative, return the set of injective symbols in its class.
    fn find_inj(&self, n: NodeID) -> &SVec<(F,AST)>;
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
                self.sel.update(&n_repr, |_, v_opt| {
                    match v_opt {
                        None => SVec::from_elem((f.clone(),t.clone()),1),
                        Some(v) => {
                            let mut v = v.clone();
                            v.push((f.clone(),t.clone()));
                            v
                        }
                    }
                });
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
