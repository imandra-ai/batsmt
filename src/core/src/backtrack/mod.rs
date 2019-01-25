
pub mod cell;
pub mod stack;
pub mod hashmap;
pub mod vec;
pub mod alloc;

/// A backtrackable component.
///
/// It gets a context `Ctx` to perform operations.
pub trait Backtrackable<Ctx> {
    /// Push one level.
    fn push_level(&mut self, _c: &mut Ctx);

    /// Backtrack `n` levels, using `ctx` to undo changes
    fn pop_levels(&mut self, _c: &mut Ctx, n: usize);
}

pub use {
    self::cell::Ref,
    self::stack::Stack,
    self::hashmap::HashMap,
    self::vec::BVec,
    self::alloc::Alloc,
};

impl<C> Backtrackable<C> for () {
    fn push_level(&mut self, _: &mut C) { }
    fn pop_levels(&mut self, _: &mut C, _n: usize) {}
}

/// Implement `Backtrackable` for a tuple of types themselves backtrackable.
macro_rules! impl_micro_theory_tuple {
    () => ();
    ( $( $t: ident ,)+ ) => {
        #[allow(non_snake_case)]
        impl<C, $( $t ,)* > Backtrackable<C> for ( $( $t ,)* )
            where $( $t : Backtrackable<C> ),*
        {
            fn push_level(&mut self, c: &mut C) {
                let ($( $t ,)*) = self;
                $(
                    $t.push_level(c);
                )*
            }

            fn pop_levels(&mut self, c: &mut C, n: usize) {
                let ($( $t ,)*) = self;
                $(
                    $t.pop_levels(c, n);
                )*
            }
        }

        impl_micro_theory_tuple_peel!{ $($t,)* }
    };
}

// recursion
macro_rules! impl_micro_theory_tuple_peel {
    ( $t0: ident, $( $t: ident,)* ) => { impl_micro_theory_tuple! { $( $t ,)* } }
}
impl_micro_theory_tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, }
