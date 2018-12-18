
#[macro_use] extern crate proptest;
extern crate batsmt_core;

use {
    std::{fmt, rc::Rc},
    fxhash::FxHashMap,
    batsmt_core::*,
    batsmt_core::ast::View,
    proptest::{prelude::*,test_runner::Config},
};

type M = AstManager<StrSymbol>;

/// Reference implementation for `ast::iter_dag`
mod ast_iter_ref {
    use super::*;

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
    pub(super) fn iter_dag_ref<F>(m: &M, t: AST, mut f: F) where F: FnMut(AST) {
        let mut seen = ast::HashSet::default();
        iter_dag_ref_rec(&mut seen, m, t, &mut f);
    }
}

mod test_ast {
    use super::*;

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
            let m = M::new();
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
            ast_iter_ref::iter_dag_ref(&m, t, |_| n2 += 1);

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
    use super::*;

    #[derive(Clone)]
    struct AstGen(Rc<AstGenCell>);

    struct AstGenCell {
        m: M,
        consts: std::cell::RefCell<FxHashMap<String, AST>>,
    }

    impl AstGen {
        fn new(m: &M) -> Self {
            AstGen(Rc::new(AstGenCell {
                m: m.clone(),
                consts: std::cell::RefCell::new(FxHashMap::default()),
            }))
        }
        fn m(&self) -> &M { &self.0.m }
        fn app(&self, f: AST, args: &[AST]) -> AST {
            self.0.m.get_mut().mk_app(f, args)
        }
        fn string(&self, s: String) -> AST {
            let c = self.0.consts.borrow();
            match c.get(&s) {
                Some(t) => *t,
                None => {
                    let t = self.0.m.get_mut().mk_string(s.clone());
                    drop(c); // before the borrow
                    self.0.consts.borrow_mut().insert(s, t);
                    t
                }
            }
        }
        fn str(&self, s: &str) -> AST { self.string(s.to_string()) }
    }

    impl fmt::Debug for AstGen {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result { write!(out, "astgen") }
    }

    fn with_astgen<F,T>(mut f: F) -> BoxedStrategy<(AstGen,T)>
        where F: FnMut(&AstGen) -> BoxedStrategy<T>, T: 'static+fmt::Debug
    {
        let m = AstGen::new(&ast::Manager::new());
        f(&m)
            .prop_map(move |t| (m.clone(), t))
            .boxed()
    }

    /// Random generator of terms
    fn gen_term(m: &AstGen) -> BoxedStrategy<AST> {
        let m = m.clone();
        let leaf = {
            let m2 = m.clone();
            "f|g|a|b|c|d".prop_map(move |s| m2.string(s))
        };
        // see https://docs.rs/proptest/*/proptest/#generating-recursive-data
        leaf.prop_recursive(
            8, 256, 10,
            move |inner| {
                let m2 = m.clone();
                (inner.clone(),prop::collection::vec(inner.clone(), 0..6)).
                    prop_map(move |(f,args)| m2.app(f,&args))
            }).boxed()
    }

    fn gen_terms(m: &AstGen, len: usize) -> BoxedStrategy<Vec<AST>> {
        prop::collection::vec(gen_term(&m), 0 .. len).boxed()
    }

    // TODO: map(id)(t) == t
    // TODO: compare iter_dag_ref and iter_dag

    // size_tree(t) >= size_dag(t)
    proptest! {
        #[test]
        fn prop_term_size(ref tup in with_astgen(gen_term)) {
            let (m,t) = tup;

            let size_tree = m.m().size_tree(*t);
            let size_dag = m.m().size_dag(*t);

            prop_assert!(size_tree >= size_dag,
                         "size tree {}, size dag {}, t: {:?}",
                         size_tree,
                         size_dag, m.m().dbg_ast(*t))
        }
    }

    // map(t, id) == t
    proptest! {
        #[test]
        fn prop_term_map_id_is_id(ref tup in with_astgen(gen_term)) {
            let (m,t) = tup;

            let u = m.m().map(*t, |m, u, view| {
                match view {
                    ast::MapView::Const => u,
                    ast::MapView::App{f, args} => {
                        m.get_mut().mk_app(*f, args)
                    },
                }
            });

            prop_assert_eq!(*t, u,
                            "t: {:?}, t.map(id): {:?}",
                            m.m().dbg_ast(*t), m.m().dbg_ast(u))
        }
    }
}

mod backtrack {
    use super::*;
    use batsmt_core::backtrack::*;

    #[test]
    fn test_stack() {
        let mut s = Stack::new();

        s.push(0);
        s.push_level();
        assert_eq!(s.n_levels(), 1);
        assert_eq!(s.as_slice(), &[0]);

        s.push(1);
        s.push(2);

        assert_eq!(s.as_slice(), &[0,1,2]);

        s.push_level();
        assert_eq!(s.n_levels(), 2);
        assert_eq!(s.as_slice(), &[0,1,2]);

        s.push(3);
        assert_eq!(s.as_slice(), &[0,1,2,3]);

        s.pop_levels(2, |x| { assert!(x > 0) });
        assert_eq!(s.n_levels(), 0);
        assert_eq!(s.as_slice(), &[0]);

        s.push_level();

        s.push(1);
        s.push(2);

        s.push_level();
        assert_eq!(s.n_levels(), 2);
        assert_eq!(s.as_slice(), &[0,1,2]);

        s.push(3);
        s.push(4);
        assert_eq!(s.as_slice(), &[0,1,2,3,4]);

        s.pop_levels(1, |x| { assert!(x >= 3) });
        assert_eq!(s.n_levels(), 1);
        assert_eq!(s.as_slice(), &[0,1,2]);

        s.pop_levels(1, |x| { assert!(x > 0) });
        assert_eq!(s.n_levels(), 0);
        assert_eq!(s.as_slice(), &[0]);
    }

    #[test]
    fn test_ref() {
        let mut s = Ref::new(0);

        *s += 1;
        s.push_level();
        assert_eq!(s.n_levels(), 1);
        assert_eq!(*s, 1);

        *s = 10;
        *s = 11;

        assert_eq!(*s, 11);

        s.push_level();
        assert_eq!(s.n_levels(), 2);
        assert_eq!(*s, 11);

        *s -= 5;
        assert_eq!(*s, 6);

        s.pop_levels(2);
        assert_eq!(s.n_levels(), 0);
        assert_eq!(*s, 1);

        s.push_level();

        *s += 10;

        s.push_level();
        assert_eq!(s.n_levels(), 2);
        assert_eq!(*s, 11);

        *s = 20;
        assert_eq!(*s, 20);

        s.pop_levels(1);
        assert_eq!(s.n_levels(), 1);
        assert_eq!(*s, 11);

        s.pop_levels(1);
        assert_eq!(s.n_levels(), 0);
        assert_eq!(*s, 1);
    }

    // ##### random tests #####

    #[derive(Clone,Debug)]
    enum Op {
        PushLevel,
        PopLevels(usize),
        Push(u32), // push object
    }

    // generator of single ops.
    // - `i` is range for elements
    // - `n` is max number of levels to remove at once
    fn stack_op() -> BoxedStrategy<Op> {
        prop_oneof![
            Just(Op::PushLevel),
            (0..200u32).prop_map(Op::Push),
            (1..5usize).prop_map(Op::PopLevels),
        ].boxed()
    }

    // check the sequence of ops is valid (doesn't pop too many levels)
    fn ops_valid(ops: &[Op]) -> bool {
        let mut lvl = 0;
        ops.iter().all(|op| match op {
            Op::Push(_) => true,
            Op::PushLevel => { lvl += 1; true },
            Op::PopLevels(n) => { let ok = *n <= lvl; if ok{lvl -= *n}; ok },
        })
    }

    // generates a vector of ops (size `i`)
    fn stack_ops(len: usize) -> BoxedStrategy<Vec<Op>> {
        prop::collection::vec(stack_op(), 0..len)
            .prop_filter("stack-invalid sequence".to_string(), |v| ops_valid(&v))
            .boxed()
    }

    // test that `ref` can be used to track the size of the `stack`
    proptest! {
        #![proptest_config(Config::with_cases(1000))]
        #[test]
        fn proptest_ref_stack(ref ops in stack_ops(100)) {
            let mut st = Stack::new();
            let mut r = Ref::new(0);

            for o in ops.iter() {
                match o {
                    Op::PushLevel => {
                        st.push_level();
                        r.push_level();
                    },
                    Op::PopLevels(n) => {
                        st.pop_levels(*n, |_| ());
                        r.pop_levels(*n);
                    },
                    Op::Push(x) => {
                        st.push(x);
                        *r += 1; // increase size of stack
                    }
                };
                // invariant to check
                prop_assert_eq!(*r.get(), st.as_slice().len());
            }
        }
    }
}
