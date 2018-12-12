
extern crate batsmt_core;
extern crate batsmt_cc;

mod cc {
    use batsmt_core::{ast,StrSymbol};
    use batsmt_cc::*;
    use std::cell::RefCell;

    #[test]
    fn test_new() {
        let m : ast::Manager<StrSymbol> = ast::Manager::new();
        let mut cc = CC::new(&m);

        // access m
        let mut m = cc.m_mut();
        m.mk_str("f");
    }

}
