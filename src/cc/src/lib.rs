
//! The core congruence closure algorithm, and a Theory built on it.
//!
//! The expected usage is, in a solver, `CCTheory::new(&manager, builtins)`

#[macro_use] extern crate log;

pub mod cc;
pub mod cc_theory;
pub mod naive_cc;
pub mod intf;
pub mod theories;

pub use {
    crate::{
        intf::{
            CC as CCInterface, CCView, Ctx, IteView, HasIte,
            InjectiveView, HasInjectivity, HasDisjointness,
            SelectorView, HasSelector, ConstructorView, HasConstructor,
            ConstructorSelectView, HasConstructorSelect,
        },
        cc::{CC, MicroTheory},
        naive_cc::NaiveCC,
        cc_theory::{CCTheory},
        theories::{Ite as ThIte, }
    },
    batsmt_theory::Actions,
};

/// a small vector of `T`.
pub(crate) type SVec<T> = smallvec::SmallVec<[T; 3]>;
pub(crate) use crate::intf::pp_t;
