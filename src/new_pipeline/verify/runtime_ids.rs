pub use crate::fact::id::FactId;

use std::fmt;

pub type PropAlgebraicPropertyId2 = u128;

// Allocated by Runtime::next_well_definedness_id (when wired).
// ByReuse cites this id; Lean lookup uses the same id to recover the WD proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WellDefinednessId2(u64);

impl WellDefinednessId2 {
    pub fn new(value: u64) -> Self {
        WellDefinednessId2(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

impl fmt::Display for WellDefinednessId2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "wd{}", self.0)
    }
}
