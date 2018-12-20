
use {
    batsmt_theory::BoolLit,
    batsat as sat,
};

/// A boolean literal
#[derive(Debug,Clone,Copy,Eq,PartialEq,Ord,PartialOrd,Hash)]
pub struct BLit(pub sat::Lit);

impl std::ops::Not for BLit {
    type Output = Self;
    fn not(self) -> Self::Output { BLit(!self.0) }
}

// BLit is a proper boolean literal
impl BoolLit for BLit {}

impl BLit {
    /// Create a literal.
    #[inline(always)]
    pub fn new(l: sat::Lit) -> Self { BLit(l) }

    /// Create a literal from a boolean variable.
    #[inline(always)]
    pub fn from_var(v: sat::Var, sign: bool) -> Self { BLit(sat::Lit::new(v,sign)) }
}

impl From<sat::Lit> for BLit {
    fn from(l: sat::Lit) -> Self { BLit::new(l) }
}
