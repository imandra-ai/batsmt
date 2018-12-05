
extern crate batsmt_core;

mod ast {
    use batsmt_core::ast::*;

    #[test]
    fn test_mk_const() {
        let mut m = AstManager::new();
        let a = m.syms_mut().mk_str("a");
        let b = m.syms_mut().mk_str("b");
        assert_ne!(a,b);
        let ta1 = m.mk_const(a);
        let ta2 = m.mk_const(a);
        assert_eq!(ta1,ta2);
        let tb1 = m.mk_const(b);
        let tb2 = m.mk_const(b);
        assert_eq!(tb1,tb2);
        assert_ne!(ta1,tb1);
        assert_ne!(ta1,tb2);
    }

    #[test]
    fn test_mk_fun() {
        let mut m = AstManager::new();
        let f = m.syms_mut().mk_str("a");
        let a = m.syms_mut().mk_str("a");
        let b = m.syms_mut().mk_str("b");
        let tf = m.mk_const(f);
        let ta = m.mk_const(a);
        let tb = m.mk_const(b);
        let t1 = m.mk_app(tf, &[ta,tb]);
        let t2 = m.mk_app(tf, &[ta,tb]);
        let t3 = m.mk_app(tf, &[tb,ta]);
        assert_eq!(t1,t2);
        assert_ne!(t1,t3);
        assert_ne!(t2,t3);
    }
}

mod symbol {
    use batsmt_core::symbol::*;

    #[test]
    fn test_mk_str() {
        let mut m = SymbolManager::new();
        let s1 = m.mk_str("a");
        let s2 = m.mk_str("a");
        assert_ne!(s1, s2);
    }

}
