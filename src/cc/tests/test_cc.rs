
#[macro_use] extern crate proptest;

use {
    std::{rc::Rc, fmt},
    fxhash::FxHashMap,
    batsmt_core::{ast,AST,StrSymbol,Symbol,backtrack::*},
    batsmt_cc::*,
    batsmt_pretty as pp,
    batsmt_theory::{BoolLit},
};

type M = ast::Manager<StrSymbol>;

// literals that are really just terms + sign.
//
// - `(true,a,b)` is `a=b`
// - `(false,a,b)` is `a!=b`
#[derive(Debug,Clone,Copy,Eq,PartialEq,Ord,PartialOrd,Hash)]
struct TermLit(bool,AST,AST);

mod term_lit {
    use super::*;

    impl TermLit {
        pub fn new(mut t1: AST, mut t2: AST, sign: bool) -> Self {
            // canonical
            if t1 > t2 {
                std::mem::swap(&mut t1, &mut t2);
            }
            TermLit(sign,t1,t2)
        }
        pub fn mk_eq(t1: AST, t2: AST) -> Self { Self::new(t1,t2,true) }
        pub fn mk_neq(t1: AST, t2: AST) -> Self { Self::new(t1,t2,false) }
        pub fn sign(&self) -> bool { self.0 }
    }

    impl std::ops::Not for TermLit {
        type Output = Self;
        fn not(self) -> Self { TermLit(!self.0, self.1, self.2) }
    }

    impl BoolLit for TermLit {}

    impl ast::PrettyM for TermLit {
        fn pp_m<S:Symbol>(&self, m: &ast::Manager<S>, ctx: &mut pp::Ctx) {
            let s = if self.sign() {" = "} else {" != "};
            ctx.pp(&m.pp(self.1)).str(s).pp(&m.pp(self.2));
        }
    }
}

type CC0 = CC<StrSymbol, TermLit>;
type NaiveCC0 = NaiveCC<StrSymbol, TermLit>;

// generate a series of operations for the congruence closure
mod prop_cc {
    use super::*;
    use proptest::{prelude::*,test_runner::Config};

    /// Context for generating terms
    #[derive(Clone)]
    struct AstGen(Rc<AstGenCell>);

    struct AstGenCell {
        m: M,
        b: Option<batsmt_cc::Builtins>,
        consts: std::cell::RefCell<FxHashMap<String, AST>>,
    }

    impl AstGenCell {
        fn string(&self, s: String) -> AST {
            let c = self.consts.borrow();
            match c.get(&s) {
                Some(t) => *t,
                None => {
                    let t = self.m.get_mut().mk_string(s.clone());
                    drop(c); // before the borrow
                    self.consts.borrow_mut().insert(s, t);
                    t
                }
            }
        }
        fn str(&self, s: &str) -> AST { self.string(s.to_string()) }
    }

    impl AstGen {
        fn new(m: &M) -> Self {
            let consts = std::cell::RefCell::new(FxHashMap::default());
            let mut cell = AstGenCell { m: m.clone(), consts, b: None, };
            // make builtins
            let b = batsmt_cc::Builtins{
                true_: cell.str("true"),
                false_: cell.str("false"),
                distinct: cell.str("distinct"),
                eq: cell.str("="),
                not_: cell.str("not"),
            };
            cell.b = Some(b);
            AstGen(Rc::new(cell))
        }
        fn m(&self) -> &M { &self.0.m }
        fn app(&self, f: AST, args: &[AST]) -> AST {
            self.0.m.get_mut().mk_app(f, args)
        }
        fn string(&self, s: String) -> AST {
            self.0.string(s)
        }
        fn b(&self) -> Builtins { self.0.b.clone().unwrap() }
    }

    // just so we can `prop_map` on it
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
            8, 512, 10,
            move |inner| {
                let m2 = m.clone();
                (inner.clone(),prop::collection::vec(inner.clone(), 0..6)).
                    prop_map(move |(f,args)| m2.app(f,&args))
            }).boxed()
    }

    prop_compose! {
        fn gen_term2(m: &AstGen)(t1 in gen_term(m), t2 in gen_term(m)) -> (AST,AST) {
            (t1,t2)
        }
    }

    /// Operation on the congruence closure
    #[derive(Clone,Debug,Copy)]
    enum Op {
        PushLevel,
        PopLevels(usize),
        AssertEq(AST,AST),
        AssertNeq(AST,AST),
        FinalCheck,
    }

    // check the sequence of ops is valid (doesn't pop too many levels)
    fn ops_valid(ops: &[Op]) -> bool {
        let mut lvl = 0;
        ops.iter().all(|op| match op {
            Op::PushLevel => { lvl += 1; true },
            Op::PopLevels(n) => { let ok = *n <= lvl; if ok{lvl -= *n}; ok },
            _ => true,
        })
    }

    fn cc_op(m: &AstGen) -> BoxedStrategy<Op> {
        prop_oneof![
            2 => Just(Op::PushLevel),
            1 => (1..5usize).prop_map(Op::PopLevels),
            6 => gen_term2(m).prop_map(|(t1,t2)| Op::AssertEq(t1,t2)),
            3 => gen_term2(m).prop_map(|(t1,t2)| Op::AssertNeq(t1,t2)),
            1 => Just(Op::FinalCheck),
        ].boxed()
    }

    // generates a vector of ops (size `i`)
    fn cc_ops(m: &AstGen, len: usize) -> BoxedStrategy<Vec<Op>> {
        prop::collection::vec(cc_op(m), 0..len)
            .prop_filter("invalid sequence of CC operations".to_string(), |v| ops_valid(&v))
            .boxed()
    }

    // use a naive CC to check this set of lits
    fn check_lits_sat<I,U>(m: &AstGen, b: Builtins, i: I) -> bool
        where I: Iterator<Item=U>, U: Into<TermLit>
    {
        let mut ncc = NaiveCC0::new(m.m(), b.clone());

        // conflict clause is a tautology,
        // so assert its negation and check for "unsat"
        for lit in i {
            let lit = lit.into();
            let TermLit(sign,t1,t2) = lit;
            if sign {
                ncc.merge(t1,t2,lit)
            } else {
                let eqn = m.app(b.eq, &[t1,t2]); // `t1=t2`
                ncc.merge(eqn, b.false_, lit)
            }
        }

        let r = ncc.final_check();
        r.is_ok()
    }

    // test that NaiveCC's backtracking behavior is consistent
    proptest! {
        #![proptest_config(Config::with_cases(100))]
        #[test]
        fn proptest_naive_cc_backtrack(ref tup in with_astgen(|m| cc_ops(m, 100))) {
            let (agen, ops) = tup;

            //println!("ops: {:?}", ops);

            let mut st = Stack::new(); // just accumulate lits
            let mut ncc = NaiveCC0::new(agen.m(), agen.b());
            let b = agen.b();

            for &op in ops.iter() {
                match op {
                    Op::PushLevel => {
                        st.push_level();
                        ncc.push_level();
                    },
                    Op::PopLevels(n) => {
                        st.pop_levels(n, |_| ());
                        ncc.pop_levels(n);
                    },
                    Op::AssertEq(t1,t2) => {
                        let lit = TermLit::mk_eq(t1,t2);
                        st.push((t1,t2,lit));
                        ncc.merge(t1,t2,lit);
                    },
                    Op::AssertNeq(t1,t2) => {
                        let lit = TermLit::mk_neq(t1,t2);
                        let eqn = agen.app(b.eq, &[t1,t2]); // term `t1=t2`
                        st.push((eqn, b.false_, lit));
                        ncc.merge(eqn, b.false_, lit);
                    },
                    Op::FinalCheck => {
                        // here be the main check
                        let r_ncc = ncc.final_check();
                        let sat1 = r_ncc.is_ok();

                        // check with a fresh ncc, without the push/pop stuff
                        let sat2 = {
                            let lits = st.iter().map(|(_,_,lit)| lit).cloned();
                            check_lits_sat(&agen, b.clone(), lits)
                        };

                        // must agree on satisfiability
                        prop_assert_eq!(sat1, sat2, "ncc-incremental.sat: {}, ncc-fresh.sat: {}", sat1, sat2);

                        // conflict returned by `ncc`, if any, must be valid
                        if let Err(confl) = r_ncc {
                            let lits = confl.0.iter().map(|lit| ! *lit);
                            let confl_sat = check_lits_sat(&agen, b.clone(), lits);

                            prop_assert!(! confl_sat, "ncc-incremental.conflict is sat");
                        }
                    }
                };
            }
        }
    }

    // test that CC and NaiveCC behave the same, and check CC conflicts
    // using naiveCC
    proptest! {
        #![proptest_config(Config::with_cases(80))]
        #[test]
        fn proptest_cc_is_correct(ref tup in with_astgen(|m| cc_ops(m, 120))) {
            let (agen, ops) = tup;

            //println!("ops: {:?}", ops);

            let mut cc = CC0::new(agen.m(), agen.b());
            let mut ncc = NaiveCC0::new(agen.m(), agen.b());
            let m = agen.m().clone();
            let b = agen.b();

            for &op in ops.iter() {
                match op {
                    Op::PushLevel => {
                        cc.push_level();
                        ncc.push_level();
                    },
                    Op::PopLevels(n) => {
                        cc.pop_levels(n);
                        ncc.pop_levels(n);
                    },
                    Op::AssertEq(t1,t2) => {
                        let lit = TermLit::mk_eq(t1,t2);
                        cc.merge(t1,t2,lit);
                        ncc.merge(t1,t2,lit);
                    },
                    Op::AssertNeq(t1,t2) => {
                        let lit = TermLit::mk_neq(t1,t2);
                        let eqn = agen.app(b.eq, &[t1,t2]); // term `t1=t2`
                        cc.merge(eqn, b.false_, lit);
                        ncc.merge(eqn, b.false_, lit);
                    },
                    Op::FinalCheck => {
                        // here be the main check
                        let r1 = cc.final_check();
                        let r2 = ncc.final_check();

                        // must agree on satisfiability
                        let sat1 = r1.is_ok();
                        let sat2 = r2.is_ok();
                        prop_assert_eq!(sat1, sat2, "cc.sat: {}, ncc.sat: {}", sat1, sat2);

                        // check conflict, too, using a fresh new naiveCC
                        if let Err(confl) = r1 {
                            let mut ncc2 = NaiveCC0::new(agen.m(), b.clone());

                            // conflict clause is a tautology,
                            // so assert its negation and check for "unsat"
                            for &lit in confl.0.iter() {
                                let lit = !lit;
                                let TermLit(sign,t1,t2) = lit;
                                if sign {
                                    ncc2.merge(t1,t2,lit)
                                } else {
                                    let eqn = agen.app(b.eq, &[t1,t2]); // `t1=t2`
                                    ncc2.merge(eqn, b.false_, lit)
                                }
                            }

                            let r = ncc2.final_check();
                            prop_assert!(r.is_err(), "conflict {:?} should be unsat", m.pp(confl.0));
                        }
                    }
                };
            }
        }
    }
}
