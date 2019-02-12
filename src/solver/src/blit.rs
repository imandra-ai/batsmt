
use {
    batsmt_theory::BoolLit,
    batsat::{self as sat, intmap::AsIndex},
};

/// A boolean literal
#[derive(Debug,Clone,Copy,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct BLit(pub sat::Lit);

pub type SatLit = sat::Lit;

impl std::ops::Not for BLit {
    type Output = Self;
    fn not(self) -> Self::Output { BLit(!self.0) }
}

// BLit is a proper boolean literal
impl BoolLit for BLit {
    #[inline(always)]
    fn abs(&self) -> Self {
        if self.0.sign() { *self } else { ! *self }
    }
}

impl BLit {
    /// Create a literal.
    #[inline(always)]
    pub fn new(l: sat::Lit) -> Self { BLit(l) }

    /// Create a literal from a boolean variable.
    #[inline(always)]
    pub fn from_var(v: sat::Var, sign: bool) -> Self { BLit(sat::Lit::new(v,sign)) }

    /// Create from a raw (signed) integer.
    /// 
    /// The integer must not be `0`, and the literal must have already
    /// been allocated in the SAT solver. Only use on integers obtained from `to_int`.
    #[inline]
    pub fn unsafe_from_int(i: i32) -> Self {
        debug_assert!(i != 0);
        BLit::from_var(sat::Var::from_index(i.abs() as usize), i > 0)
    }

    /// Convert the literal into a raw integer.
    /// 
    /// Only use in conjunction with `unsafe_from_int`.
    #[inline]
    pub fn to_int(&self) -> i32 {
        let i = self.0.var().as_index() as i32;
        if self.0.sign() { i } else { -i }
    }
}

impl From<sat::Lit> for BLit {
    fn from(l: sat::Lit) -> Self { BLit::new(l) }
}
