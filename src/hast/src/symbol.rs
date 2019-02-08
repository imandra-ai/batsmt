
use {
    batsmt_core::{gc, },
    batsmt_pretty as pp,
};

/// Context with a notion of symbols and symbol manager.
pub trait SymbolCtx {
    /// A reference to a symbol in the manager.
    type Ref : Copy + Sized;

    /// A temporary view of a symbol.
    type View : std::fmt::Display + ?Sized;

    /// Something to build a symbol from
    type Builder;

    /// The symbol manager.
    type SymM : SymbolManager<View=Self::View, Builder=Self::Builder,Ref=Self::Ref>;
}

/// The interface for a representation of logic symbols.
///
/// Symbols should be any unique object that belongs
/// to the logic signature, set of sorts, custom domain elements
/// (such as arithmetic constants, datatype constructors, etc.).
pub trait SymbolManager
    : Sized + gc::HasInternalMemory
    + SymbolCtx<SymM=Self>
    + for<'a> pp::Pretty1<&'a <Self as SymbolCtx>::View>
{
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

    /// Sentinel reference. Must not be dereferenced ever.
    fn sentinel(&self) -> Self::Ref;
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

    impl SymbolCtx for StrManager {
        type Ref = u32;
        type View = str;
        type Builder = Rc<str>;
        type SymM = StrManager;
    }

    impl SymbolManager for StrManager {
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

        fn sentinel(&self) -> Self::Ref { u32::MAX }
    }

    impl<'a> pp::Pretty1<&'a str> for StrManager {
        // SMTLIB printing
        fn pp1_into(&self, s: &&'a str, ctx: &mut pp::Ctx) {
            let escape = s.contains(|c| {c == ' ' || c == '\n'});
            if escape { ctx.str("|"); }
            ctx.string(s.to_string());
            if escape { ctx.str("|"); }
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
}

/*
/// String + integer symbols
pub mod str_id {
    use {
        super::*, std::fmt,
        fxhash::FxHashMap,
        std::{u32, rc::Rc},
    };

    /// Symbols are either:
    /// - generative (creation
    #[derive(Copy,Clone,Eq,PartialEq,Hash)]
    pub enum Kind { Nominal, Generative }

    #[derive(Clone)]
    pub struct Sym {
        id: u32,
        kind: Kind,
        name: Rc<str>,
    }

    impl fmt::Display for Sym {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "{}/{}", self.name, self.id)
        }
    }

    pub type Builder = (Kind, Rc<str>);

    /// Manager for string+id symbols.
    ///
    /// This manager uses scoped names as symbols.
    /// Each symbol has a unique integer and a string name.
    pub struct ScopedManager {
        sentinel: Rc<str>, // used to fill empty slots
        by_name: FxHashMap<Rc<str>, u32>, // find by name
        syms: Vec<Sym>,
        recycle: Vec<u32>, // ids to recycle
    }

    impl SymbolCtx for ScopedManager {
        type Ref = u32;
        type View = Sym;
        type Builder = Rc<str>;
        type SymM = ScopedManager;
    }

    impl SymbolManager for ScopedManager {
        /// Build a new manager.
        fn new() -> Self {
            ScopedManager {
                syms: vec!(),
                by_name: FxHashMap::default(),
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
            match self.tbl.get(s.str) {
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

        fn sentinel(&self) -> Self::Ref { u32::MAX }
    }

    impl<'a> pp::Pretty1<&'a Sym> for ScopedManager {
        // SMTLIB printing
        fn pp1_into(&self, s: &&'a Sym, ctx: &mut pp::Ctx) {
            let escape = s.name.contains(|c| {c == ' ' || c == '\n'});
            if escape { ctx.str("|"); }
            ctx.string(s.to_string());
            if escape { ctx.str("|"); }
        }
    }

    impl gc::HasInternalMemory for ScopedManager {
        fn reclaim_unused_memory(&mut self) {
            self.syms.shrink_to_fit();
            self.recycle.shrink_to_fit();
        }
    }

    impl ScopedManager {
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
}
*/
