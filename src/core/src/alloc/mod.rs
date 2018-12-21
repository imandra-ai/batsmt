
//! Specialized allocators.

pub mod append_only_array;

pub use {
    self::append_only_array::Alloc as AppendOnlyArrayAlloc,
};
