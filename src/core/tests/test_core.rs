
extern crate batsmt_core;

mod ast {
    use batsmt_core::*;
    use batsmt_core::AstView as View;

    type M = AstManager<StrSymbol>;

    #[test]
    fn test_mk_str() {
        let m = M::new();
        let a = m.mk_str("a");
        let b = m.mk_str("b");
        assert_ne!(a,b);
        let a2 = m.mk_str("a");
        assert_ne!(a,a2);
    }

    #[test]
    fn test_view_const() {
        let m = M::new();
        let a = m.mk_str("a");
        let b = m.mk_str("b");
        assert!(match m.get().view(a) { View::Const(s) => s == "a", _ => false });
        assert!(match m.get().view(b) { View::Const(s) => s == "b", _ => false });
    }

    #[test]
    fn test_mk_fun() {
        let m = M::new();
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
    fn test_view() {
        let m = M::new();
        let mut m = m.get_mut();
        let f = m.mk_str("f");
        let g = m.mk_str("g");
        let a = m.mk_str("a");
        let b = m.mk_str("b");
        let t1 = m.mk_app(f, &[a,b]);
        let t2 = m.mk_app(f, &[b,a]);
        let t4 = m.mk_app(g, &[t1]);
        assert!(match m.view(t1) { View::App{f:f2, args} => f2 == f && args==&[a,b], _ => false });
        assert!(match m.view(t2) { View::App{f:f2, args} => f2 == f && args==&[b,a], _ => false });
        assert!(match m.view(t4) { View::App{f:f2, args} => f2 == g && args==&[t1], _ => false });
        let t10 = m.mk_app(f, &[a; 10]);
        let t11 = m.mk_app(f, &[b; 10]);
        assert!(match m.view(t10) { View::App{f:f2, args} => f2 == f && args==&[a;10], _ => false });
        assert!(match m.view(t11) { View::App{f:f2, args} => f2 == f && args==&[b;10], _ => false });
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

        let mut m = s.m.get_mut();
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
    fn test_bitset_add_rm() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();
        let mut bs = AstBitSet::new();
        for &t in s.terms.iter() {
            assert!(! bs.get(t));
            bs.add(t);
        }
        for &t in s.terms.iter() {
            assert!(bs.get(t));
        }
        for &t in s.terms.iter() {
            bs.remove(t);
        }
        for &t in s.terms.iter() {
            assert!(! bs.get(t));
        }
    }

    #[test]
    fn test_bitset_clear() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();
        let mut bs = AstBitSet::new();
        bs.add_slice(&s.terms);
        for &t in s.terms.iter() {
            assert!(bs.get(t));
        }
        bs.clear();
        for &t in s.terms.iter() {
            assert!(! bs.get(t));
        }
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
    fn test_dense_map() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();

        let mut m : AstDenseMap<usize> = AstDenseMap::new(0);

        for (i,&t) in s.terms.iter().enumerate() {
            assert!(! m.contains(t));

            m.insert(t,i);
        }

        // ahah just kidding
        m.clear();
        assert!(m.is_empty());
        assert_eq!(0, m.len());

        for (i,&t) in s.terms.iter().enumerate() {
            assert!(! m.contains(t));

            m.insert(t,i);
        }

        // now check membership
        for (i,&t) in s.terms.iter().enumerate() {
            assert!(m.contains(t));
            assert_eq!(m.get(t), Some(&i));
        }

        assert_eq!(m.len(), m.iter().count());
    }


    fn iter_dag_ref_rec<F>(seen: &mut ast::HashSet, m: &M, t: AST, f: &mut F) where F:FnMut(AST) {
        if ! seen.contains(&t) {
            seen.insert(t);
            f(t);

            let mr = m.get();
            match mr.view(t) {
                View::Const(_) => (),
                View::App{f: f0,args} => {
                    iter_dag_ref_rec(seen, m, f0, f);
                    for a in args.iter() {
                        iter_dag_ref_rec(seen, m, *a, f);
                    }
                }
            }
        }
    }

    // trivial implementation of `iter_dag`, as a reference
    fn iter_dag_ref<F>(m: &M, t: AST, mut f: F) where F: FnMut(AST) {
        let mut seen = ast::HashSet::default();

        iter_dag_ref_rec(&mut seen, m, t, &mut f);
    }

    #[test]
    fn test_iter_dag() {
        // create a bunch of terms
        let mut s = StressApp::new(100).verbose(false).long_apps(true);
        s.run();
        let m = s.m.clone();

        for &t in s.terms.iter() {
            // count subterms using `iter_dag`
            let mut n1 = 0;
            m.iter_dag(t, |_| n1 += 1);

            let mut n2 = 0;
            iter_dag_ref(&m, t, |_| n2 += 1);

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

