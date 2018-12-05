
//! Main Interface for GC

/// The trait for managers that support Garbage Collection of their content
pub trait GC {
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

