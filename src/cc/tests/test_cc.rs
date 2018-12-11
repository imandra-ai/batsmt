
extern crate batsmt_core;
extern crate batsmt_cc;

mod cc {
    use batsmt_core::{ast,StrSymbol};
    use batsmt_cc::*;
    use std::cell::RefCell;

    #[test]
    fn test_new() {
        let m = RefCell::new(ast::Manager::new() as ast::Manager<StrSymbol>);
        let cc = CC::new(m);

        // access m
        let mut m = cc.m_mut();
        m.mk_str("f");
    }

}
