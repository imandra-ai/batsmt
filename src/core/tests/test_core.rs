
#[macro_use] extern crate proptest;
extern crate batsmt_core;

use {
    proptest::{prelude::*,test_runner::Config},
};

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
