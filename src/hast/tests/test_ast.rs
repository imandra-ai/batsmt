
#[macro_use] extern crate proptest;
extern crate batsmt_core;
extern crate batsmt_hast;

use {
    std::{fmt, rc::Rc}, 
    batsmt_core::{
        ast_u32::{self, AST, },
        ast::{self, View}, },
    fxhash::FxHashMap,
    batsmt_hast::{HManager, StrSymbolManager,}
};

type M = HManager<StrSymbolManager>;

/// Reference implementation for `ast::iter_dag`
mod ast_iter_ref {
    use {super::*, batsmt_core::ast::{AstSet, Manager, } };

    fn iter_dag_ref_rec<F>(seen: &mut ast_u32::HashSet, m: &M, t: AST, f: &mut F) where F:FnMut(&M, AST) {
        if ! seen.contains(&t) {
            seen.add(t);
            f(&m, t);

            match m.view(&t) {
                View::Const(_) => (),
                View::App{f: f0,args} => {
                    iter_dag_ref_rec(seen, m, *f0, f);
                    for a in args.iter() {
                        iter_dag_ref_rec(seen, m, *a, f);
                    }
                }
            }
        }
    }

    // trivial implementation of `iter_dag`, as a reference
    pub(super) fn iter_dag_ref<F>(m: &M, t: AST, mut f: F) where F: FnMut(&M, AST) {
        let mut seen = ast_u32::HashSet::new();
        iter_dag_ref_rec(&mut seen, m, t, &mut f);
    }
}

mod test_ast {
    use {super::*, batsmt_core::{gc::GC,ast::{Manager}} };

    #[test]
    fn test_mk_str() {
        let mut m = M::new();
        let a = m.mk_str("a");
        let b = m.mk_str("b");
        assert_ne!(a,b);
        let a2 = m.mk_str("a");
        assert_ne!(a,a2);
    }

    #[test]
    fn test_view_const() {
        let mut m = M::new();
        let a = m.mk_str("a");
        let b = m.mk_str("b");
        assert!(match m.view(&a) { View::Const(s) => s == "a", _ => false });
        assert!(match m.view(&b) { View::Const(s) => s == "b", _ => false });
    }

    #[test]
    fn test_mk_fun() {
        let mut m = M::new();
        let f = m.mk_str("f");
        let g = m.mk_str("g");
        let a = m.mk_str("a");
        let b = m.mk_str("b");
        let t1 = m.mk_app(f, &[a,b]);
        let t2 = m.mk_app(f, &[a,b]);
        let t3 = m.mk_app(f, &[b,a]);
        let t4 = m.mk_app(g, &[t1]);
        let t5 = m.mk_app(g, &[t2]);
        assert_eq!(t1,t2);
        assert_ne!(t1,t3);
        assert_ne!(t2,t3);
        assert_eq!(t4,t5);

        let t10 = m.mk_app(f, &[a; 10]);
        let t11 = m.mk_app(f, &[a; 10]);
        let t12 = m.mk_app(f, &[b; 10]);
        assert_eq!(t10,t11);
        assert_ne!(t10,t12);
    }

    #[test]
    fn test_const_not_hashconsing() {
        let mut m = M::new();
        let a1 = m.mk_str("a");
        let a2 = m.mk_str("a");
        assert_ne!(a1, a2);
    }

    #[test]
    fn test_view() {
        let mut m = M::new();
        let f = m.mk_str("f");
        let g = m.mk_str("g");
        let a = m.mk_str("a");
        let b = m.mk_str("b");
        let t1 = m.mk_app(f, &[a,b]);
        let t2 = m.mk_app(f, &[b,a]);
        let t4 = m.mk_app(g, &[t1]);
        assert!(match m.view(&t1) { View::App{f:f2, args} => *f2 == f && args==&[a,b], _ => false });
        assert!(match m.view(&t2) { View::App{f:f2, args} => *f2 == f && args==&[b,a], _ => false });
        assert!(match m.view(&t4) { View::App{f:f2, args} => *f2 == g && args==&[t1], _ => false });
        let t10 = m.mk_app(f, &[a; 10]);
        let t11 = m.mk_app(f, &[b; 10]);
        assert!(match m.view(&t10) { View::App{f:f2, args} => *f2 == f && args==&[a;10], _ => false });
        assert!(match m.view(&t11) { View::App{f:f2, args} => *f2 == f && args==&[b;10], _ => false });
    }

    struct StressApp {
        n: usize,
        long_apps: bool,
        verbose: bool,
        m: M,
        f: AST,
        g: AST,
        a: AST,
        b: AST,
        terms: Vec<AST>,
    }

    fn mk_stress_app(s: &mut StressApp) {
        use std::time::Instant;

        let m = &mut s.m;
        let f = s.f;
        let g = s.g;
        let mut n_app_created = 0;
        let start = Instant::now();
        let terms = &mut s.terms;
        {
            // create a bunch of terms
            let mut i = 0;
            let mut tmp = vec![];
            while terms.len () < s.n {
                for &t1 in terms[i..].iter() {
                    for &t2 in terms.iter() {
                        let t = m.mk_app(f, &[t1,t2]);
                        tmp.push(t);
                        n_app_created += 1;
                        let t = m.mk_app(g, &[t1,t2]);
                        tmp.push(t);
                        n_app_created += 1;
                    }

                    if s.long_apps {
                        let t = m.mk_app(f, &[t1; 5]);
                        tmp.push(t);
                        n_app_created += 1;
                        let t = m.mk_app(g, &[t1; 5]);
                        tmp.push(t);
                        n_app_created += 1;
                    }
                }
                i = terms.len();
                terms.extend(&tmp);
                tmp.clear();
            }
        }
        let duration = Instant::now() - start;
        if s.verbose {
            let dur_as_f =
                duration.as_secs() as f64 + (duration.subsec_micros() as f64 * 1e-6);
            eprintln!("took {:?} to create {} applications \
                      (including long ones: {}, {} in manager, {}/s)",
                duration, n_app_created, s.long_apps, m.n_terms(),
                n_app_created as f64 / dur_as_f);
        }
    }

    impl StressApp {
        fn new(n: usize) -> Self {
            let mut m = M::new();
            let f = m.mk_str("f");
            let g = m.mk_str("g");
            let a = m.mk_str("a");
            let b = m.mk_str("b");
            let terms = vec![a,b];
            StressApp{n, long_apps: false, verbose: false, f, g, a, b, m, terms, }
        }
        fn reset(&mut self) { self.terms = vec![self.a, self.b] }
        fn long_apps(mut self, b: bool) -> Self { self.long_apps = b; self }
        fn verbose(mut self, b: bool) -> Self { self.verbose = b; self }
        fn run(&mut self) { self.reset(); mk_stress_app(self) }
    }

    #[test]
    fn test_stress_apps() {
        StressApp::new(100).verbose(true).long_apps(false).run();
        StressApp::new(100).verbose(true).long_apps(true).run();
        StressApp::new(1000).verbose(true).long_apps(false).run();
        StressApp::new(1000).verbose(true).long_apps(true).run();
    }

    #[test]
    fn test_gc() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();

        let alive = s.terms[..10].iter().map(|a| *a).collect::<Vec<AST>>();
        {
            let m = &mut s.m;
            // mark & collect
            for t in alive.iter() {
                m.mark_root(t);
            }
            let n_collected = m.collect();
            // NOTE: because terms that come later in `terms` are created later,
            // they must all have been collected.
            assert_eq!(s.terms.len() - alive.len(), n_collected);
        }

        {
            // test that we can still create terms
            let m = &mut s.m;
            let f = s.f;
            let a = alive[8]; // last terms, their application should be dead
            let b = alive[9];
            assert_ne!(a,b);
            let t1 = m.mk_app(f, &[a,b]);
            let t2 = m.mk_app(f, &[a,b]);
            let t3 = m.mk_app(f, &[b,a]);
            assert_eq!(t1, t2);
            assert_ne!(t1, t3);
            s.terms.push(t1);
            s.terms.push(t3);
        }

        {
            s.run();

            let alive = s.terms[..10].iter().collect::<Vec<_>>();

            // again
            let m = &mut s.m;
            // mark & collect
            for t in alive.iter() {
                m.mark_root(t);
            }
            let n = m.collect();
            assert!(n > 2);
        }

        {
            // create terms again, to check nothing is messed up
            s.run();
        }
    }

    #[test]
    fn test_iter_dag() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();
        let m = &s.m;

        for &t in s.terms.iter() {
            // count subterms using `iter_dag`
            let mut n1 = 0;
            ast::iter_dag(m, &t, |_,_| n1 += 1);

            let mut n2 = 0;
            ast_iter_ref::iter_dag_ref(m, t, |_,_| n2 += 1);

            assert_eq!(n1, n2);
        }
    }

    /* FIXME:
    // test that `t.map(id) == t`
    #[test]
    fn test_map_dag_id() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();
        let m = s.m.clone();

        for t in s.terms.iter() {
            let u = m.map(t, |x| x);
            assert_eq!(t, u);
        }

    }

    // test that `t.map(|f| f.args.rev()).map(|f| f.args.rev()) == t`
    #[test]
    fn test_map_dag_rev() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();
        let m = s.m.clone();

        fn rev_args(m: &M, t: AST) -> AST {
            let m = m.clone();
            m.map(t, |m, t| {
                m.get_mut().

            }
        }

        for t in s.terms.iter() {
            let u = m.map(t, |x| x);
            assert_eq!(t, u);
        }

    }
    */
}

mod ast_prop {
    use {
        super::*, batsmt_pretty::Pretty1,
        batsmt_core::ast::{AstSet, Manager},
        proptest::prelude::*,
    };

    #[derive(Clone)]
    struct AstGen(Rc<std::cell::RefCell<AstGenCell>>);
    struct AstGenCell {
        m: M,
        consts: FxHashMap<String, AST>,
    }

    impl ast::HasManager for AstGenCell {
        type M = M;
        fn m(&self) -> &M { &self.m }
        fn m_mut(&mut self) -> &mut M { &mut self.m }
    }

    impl AstGen {
        fn new(m: M) -> Self {
            AstGen(Rc::new(std::cell::RefCell::new(AstGenCell{
                m, consts: FxHashMap::default(),
            })))
        }
        fn app(&self, f: AST, args: &[AST]) -> AST {
            self.0.borrow_mut().m.mk_app(f, args)
        }
        fn string(&self, s: String) -> AST {
            let mut c = self.0.borrow_mut();;
            match c.consts.get(&s) {
                Some(t) => *t,
                None => {
                    let t = c.m.mk_string(s.clone());
                    c.consts.insert(s, t);
                    t
                }
            }
        }
    }

    impl fmt::Debug for AstGen {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result { write!(out, "astgen") }
    }

    fn with_astgen<F,T>(mut f: F) -> BoxedStrategy<(AstGen,T)>
        where F: FnMut(&AstGen) -> BoxedStrategy<T>, T: 'static+fmt::Debug
    {
        let m = AstGen::new(HManager::new());
        f(&m).prop_map(move |t| (m.clone(), t)) .boxed()
    }

    /// Random generator of terms
    fn gen_term(m: &AstGen) -> BoxedStrategy<AST> {
        let m = m.clone();
        let leaf = {
            let m2 = m.clone();
            "f|g|a|b|c|d".prop_map(move |s| m2.string(s)).boxed()
        };
        // see https://docs.rs/proptest/*/proptest/#generating-recursive-data
        leaf.prop_recursive(
            10, 512, 10,
            move |inner| {
                let m2 = m.clone();
                (inner.clone(),prop::collection::vec(inner.clone(), 0..6)).
                    prop_map(move |(f,args)| m2.app(f,&args))
            }).boxed()
    }

    // size_tree(t) >= size_dag(t)
    proptest! {
        #[test]
        fn prop_term_size(ref mut tup in with_astgen(gen_term)) {
            let (m,t) = tup;

            let m = &mut m.0.borrow_mut().m;

            let size_tree = ast_u32::ast_size_tree(m, t);
            let size_dag = ast::size_dag(m, t);

            prop_assert!(size_tree >= size_dag,
                         "size tree {}, size dag {}, t: {:?}",
                         size_tree,
                         size_dag, m.pp(&t))
        }
    }

    // map(t, id) == t
    proptest! {
        #[test]
        fn prop_term_map_id_is_id(ref tup in with_astgen(gen_term)) {
            let (m,t) = tup;
            let m = &mut m.0.borrow_mut().m;

            let u = ast::map_dag(m, t, |_| (), |m, u, view: ast::View<(),AST>| {
                match view {
                    ast::View::Const(()) => *u,
                    ast::View::App{f, args} => {
                        m.mk_app(*f, args)
                    },
                }
            });

            prop_assert_eq!(*t, u,
                            "t: {:?}, t.map(id): {:?}",
                            m.pp(t), m.pp(&u))
        }
    }

    // iter_dag_ref and iter_dag are the same
    proptest! {
        #[test]
        fn prop_iter_dag_ref(ref tup in with_astgen(gen_term)) {
            let (m,t) = tup;
            let m = &mut m.0.borrow_mut().m;

            let mut n1 = 0;
            let mut n2 = 0;

            ast::iter_dag(m, t, |_,_| { n1 += 1 });
            ast_iter_ref::iter_dag_ref(m, *t, |_,_| { n2 += 1 });

            prop_assert!(n1 == n2, "same size, t: {:?}", m.pp(t))
        }
    }

    // iter_dag and iter_suffix traverse same set of terms
    proptest! {
        #[test]
        fn prop_iter_dag_and_iter_suffix_same_set_of_subterms(ref tup in with_astgen(gen_term)) {
            let (m,t) = tup;
            let m = &mut m.0.borrow_mut().m;

            let mut seen1 = vec!();
            let mut seen2 = vec!();

            ast::iter_dag(m, t, |_,u| { seen1.push(*u) });
            ast::iter_suffix(m, t, &mut(), |_,_,_| true, |_,_,u| { seen2.push(*u) });

            seen1.sort();
            seen2.sort();

            prop_assert!(&seen1 == &seen2,
                         "same traversal, t: {:?}", m.pp(t))
        }
    }

    // iter_suffix traverses subterms before superterms
    proptest! {
        #[test]
        fn prop_iter_suffix_subterms_first(ref tup in with_astgen(gen_term)) {
            let (m,t) = tup;
            let m = &mut m.0.borrow_mut().m;

            let mut seen = ast::HashSet::new();

            let mut res = None; // for fast exit
            ast::iter_suffix(m, t, &mut res, |_,r,_| r.is_some(), |m,r,u| {
                // immediate subterms
                let subs: Vec<_> = m.view(u).subterms().cloned().collect();
                for v in &subs {
                    if ! seen.contains(v) {
                        *r = Some((*t, *u, *v));
                    }
                    if r.is_some() { break }
                }
                seen.add(*t);
            });

            if let Some((t,u,v)) = res {
                prop_assert!(false,
                "traversing {:?}\nsubterm {:?}\nseen should contain {:?}\nseen: {:?}",
                m.pp(&t),
                m.pp(&u),
                m.pp(&v),
                &seen);
            }
            prop_assert!(true)
        }
    }
}
