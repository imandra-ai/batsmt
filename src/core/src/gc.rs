
//! Main Interface for GC

use {std::collections::{HashMap, }};

pub trait HasInternalMemory {
    /// Free unused internal memory, as much as possible.
    ///
    /// This includes:
    /// - clearing caches
    /// - shrinking internal structures (maps, tables, etc.)
    /// - compacting internal allocators
    fn reclaim_unused_memory(&mut self);
}

/// The trait for managers that support Garbage Collection of their content.
///
/// This must also implement `HasInternalMemory`; the typical usage would
/// be to mark roots, collect, then free internal memory.
pub trait GC : HasInternalMemory {
    type Element;

    /// Mark the given element as a root used by the rest of the program
    fn mark_root(&mut self, e: &Self::Element);

    /// Collect unused elements, return the number of collected elements.
    ///
    /// Also has the side effect of clearing the set of roots.
    /// One should *always* call `mark_root` with all the roots every time
    /// before calling `collect`
    fn collect(&mut self) -> usize;
}

impl<T> HasInternalMemory for Vec<T> {
    fn reclaim_unused_memory(&mut self) { self.shrink_to_fit() }
}

impl<K:Eq+std::hash::Hash,V> HasInternalMemory for HashMap<K,V> {
    fn reclaim_unused_memory(&mut self) { self.shrink_to_fit() }
}
