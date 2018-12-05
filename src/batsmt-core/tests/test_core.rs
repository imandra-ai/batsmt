
extern crate batsmt_core;

mod ast {
    use batsmt_core::ast::*;

    #[test]
    fn test_mk_const() {
        let mut m = AstManager::new();
        let a = m.mk_const("a");
        let b = m.mk_const("b");
        assert_ne!(a,b);
        let a2 = m.mk_const("a");
        assert_ne!(a,a2);
    }

    #[test]
    fn test_view_const() {
        let mut m = AstManager::new();
        let a = m.mk_const("a");
        let b = m.mk_const("b");
        assert!(match m.view(a) { View::Const(s) => s.eq_str("a"), _ => false });
        assert!(match m.view(b) { View::Const(s) => s.eq_str("b"), _ => false });
    }

    #[test]
    fn test_mk_fun() {
        let mut m = AstManager::new();
        let f = m.mk_const("f");
        let g = m.mk_const("g");
        let a = m.mk_const("a");
        let b = m.mk_const("b");
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
        let mut m = AstManager::new();
        let f = m.mk_const("f");
        let g = m.mk_const("g");
        let a = m.mk_const("a");
        let b = m.mk_const("b");
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
}
