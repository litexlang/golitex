//! Top-level fact verification result: mirrors `Fact` shape (plus Unknown).
//!
//! Proof *methods* (cache, builtin, let-binding, closed numeric, …) live inside
//! each shape's payload — not as siblings of AtomicFact / ForallFact.

use super::verify_atomic_fact::VerifyAtomicFactResult;

pub enum VerifyFactResult {
    Unknown(UnknownVerifyFactResult),
    AtomicFact(Box<VerifyAtomicFactResult>),
    AndFact(Box<VerifyAndFactResult>),
    ChainFact(Box<VerifyChainFactResult>),
    OrFact(Box<VerifyOrFactResult>),
    ExistFact(Box<VerifyExistFactResult>),
    ForallFact(Box<VerifyForallFactResult>),
    ForallFactWithIff(Box<VerifyForallFactWithIffResult>),
    NotForall(Box<VerifyNotForallFactResult>),
}

pub enum UnknownVerifyFactResult {
    WellDefinedKnown,
    UnableToSearchProof,
}

// Composite / quantified payloads: shape is fixed; bodies fill in as those
// pipelines are attached to this module tree (draft files already exist).
pub struct VerifyAndFactResult {
    pub _wire: (),
}

pub struct VerifyChainFactResult {
    pub _wire: (),
}

pub struct VerifyOrFactResult {
    pub _wire: (),
}

pub struct VerifyExistFactResult {
    pub _wire: (),
}

pub struct VerifyForallFactResult {
    pub _wire: (),
}

pub struct VerifyForallFactWithIffResult {
    pub _wire: (),
}

pub struct VerifyNotForallFactResult {
    pub _wire: (),
}

impl VerifyFactResult {
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }
}
