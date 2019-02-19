
//! Micro theories

mod th_ite;
mod th_injectivity;
mod th_disjointness;
mod th_selector;

pub use {
    th_ite::Ite,
    th_injectivity::Injectivity,
    th_disjointness::Disjointness,
    th_selector::Selector,
};

/// A local small-vec
pub(crate) type SVec<T> = smallvec::SmallVec<[T; 4]>;
