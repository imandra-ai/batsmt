
//! Micro theories

mod th_ite;
mod th_injectivity;
mod th_disjointness;
mod th_selector;
mod th_constructor;
mod th_constructor_select;

pub use {
    th_ite::Ite,
    th_injectivity::Injectivity,
    th_disjointness::Disjointness,
    th_selector::Selector,
    th_constructor::Constructor,
    th_constructor_select::ConstructorSelect,
};

/// A local small-vec
pub(crate) type SVec<T> = smallvec::SmallVec<[T; 4]>;
