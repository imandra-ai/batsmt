
//! The core congruence closure algorithm, and a Theory built on it.
//!
//! The expected usage is, in a solver, `CCTheory::new(&manager, builtins)`

#[macro_use] extern crate log;

pub mod cc;
pub mod cc_theory;
pub mod naive_cc;
pub(crate) mod types;
pub mod intf;

pub use {
    crate::{
        types::{ Builtins, PropagationSet, SVec, Conflict, Ctx, },
        intf::{CC as CCInterface},
        cc::CC,
        naive_cc::NaiveCC,
        cc_theory::{CCTheory},
    },
};
