
use {
    batsmt_core::{gc, }
};

/// Context with a notion of symbols and symbol manager.
pub trait SymbolCtx {
    /// A reference to a symbol in the manager.
    type SymRef : Copy + Sized;

    /// A temporary view of a symbol.
    type SymView : std::fmt::Debug + ?Sized;

    /// Something to build a symbol from
    type SymBuilder;

    /// The symbol manager.
    type SymM : 'static + SymbolManager<View=Self::SymView, Builder=Self::SymBuilder,Ref=Self::SymRef>;
}

/// The interface for a representation of logic symbols.
///
/// Symbols should be any unique object that belongs
/// to the logic signature, set of sorts, custom domain elements
/// (such as arithmetic constants, datatype constructors, etc.).
pub trait SymbolManager : gc::HasInternalMemory {
    /// A reference to a symbol in the manager.
    type Ref : Copy + Sized;

    /// A temporary view of a symbol.
    type View : std::fmt::Debug + ?Sized;

    /// Something to build a symbol from
    type Builder;

    /// Build a new manager.
    fn new() -> Self;

    /// Get a temporary view of the raw reference.
    fn view(&self, r: Self::Ref) -> &Self::View;

    /// Build a new symbol from the given symbol builder.
    fn build<U>(&mut self, b: U) -> Self::Ref
        where U: std::borrow::Borrow<Self::View> + Into<Self::Builder>;

    /// Free resources, given a reference.
    ///
    /// The caller must never use this reference again.
    fn free(&mut self, r: Self::Ref);
}

/// String symbols
pub mod str {
    use {
        super::*,
        fxhash::FxHashMap,
        std::{u32, rc::Rc},
    };

    /// Manager for string symbols.
    ///
    /// This manager uses interned strings as symbols. Each string has a
    /// unique representation inside it, and uses a unique integer ID
    /// as a reference.
    pub struct StrManager {
        sentinel: Rc<str>, // used to fill empty slots
        tbl: FxHashMap<Rc<str>, u32>,
        syms: Vec<Rc<str>>,
        recycle: Vec<u32>, // ids to recycle
    }

    impl SymbolManager for StrManager {
        type Ref = u32;
        type View = str;
        type Builder = Rc<str>;

        /// Build a new manager.
        fn new() -> Self {
            StrManager {
                tbl: FxHashMap::default(), syms: vec!(),
                sentinel: "SENTINEL".into(),
                recycle: vec!(),
            }
        }

        /// Get a temporary view of the raw reference.
        #[inline(always)]
        fn view(&self, r: Self::Ref) -> &Self::View {
            &self.syms[r as usize]
        }

        /// Build a new symbol from the given symbol builder.
        fn build<U>(&mut self, b: U) -> Self::Ref
            where U: std::borrow::Borrow<Self::View> + Into<Self::Builder>
        {
            let s = b.borrow();
            match self.tbl.get(s) {
                Some(r) => *r, // found
                None => {
                    // insert new symbol.
                    let owned: Self::Builder = s.into();
                    let r = self.allocate_new_id();
                    self.tbl.insert(owned.clone(), r);
                    self.syms.push(owned);
                    r
                }
            }
        }

        /// Free resources, given a reference.
        ///
        /// The caller must never use this reference again.
        fn free(&mut self, r: Self::Ref) {
            let s: &str = &self.syms[r as usize];
            self.tbl.remove(s);
            self.syms[r as usize] = self.sentinel.clone(); // remove from array
            self.recycle.push(r); // re-use this ID in the future
        }
    }

    impl gc::HasInternalMemory for StrManager {
        fn reclaim_unused_memory(&mut self) {
            self.tbl.shrink_to_fit();
            self.syms.shrink_to_fit();
            self.recycle.shrink_to_fit();
        }
    }

    impl StrManager {
        fn allocate_new_id(&mut self) -> u32 {
            if let Some(r) = self.recycle.pop() {
                r
            } else {
                let r = self.syms.len();
                if r > u32::MAX as usize {
                    panic!("allocated too many symbols (over {})", u32::MAX);
                }
                r as u32
            }
        }
    }

    /// A basic implementation: just a string
    #[derive(Copy,Clone,Eq,PartialEq,Hash,Ord,PartialOrd)]
    struct Ptr {
        ptr: *const u8,
        len: usize,
    }

    /* FIXME: how to print in SMTLIB…
    impl<'a> pp::Pretty for &'a str {
        fn pp(&'a self, ctx: &mut pp::Ctx) {
            let escape = self.contains(|c| {c == ' ' || c == '\n'});
            if escape { ctx.str("|"); }
            ctx.string(self.to_string());
            if escape { ctx.str("|"); }
        }
    }
    */
}
