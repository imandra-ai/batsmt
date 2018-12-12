
//! The core congruence closure algorithm, and a Theory built on it.
//!
//! The expected usage is, in a solver, `CCTheory::new(&manager, builtins)`

extern crate batsmt_core;
extern crate smallvec;
#[macro_use] extern crate log;

pub mod cc;
pub mod cc_theory;

pub use {
    crate::{
        cc::{CC, Conflict, Propagation, SVec},
        cc_theory::{CCTheory, Builtins},
    },
};

