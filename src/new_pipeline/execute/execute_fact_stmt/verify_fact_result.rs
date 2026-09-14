//! Top-level fact verification result.
//!
//! Mirrors `Fact` for compound shapes; atomic facts are flattened into
//! `Equality` / `AtomicExceptEquality` (no intermediate AtomicFact layer).
//!
//! Verify entry points return `RuntimeResult<VerifyFactResult>`:
//! - `Ok(Unknown)` = unable to prove (not a runtime error)
//! - `Err` = real operational / invariant failure

use super::verify_atomic_fact::{VerifyAtomicExceptEqualityFactResult, VerifyEqualityResult};

pub enum VerifyFactResult {
    Unknown(UnknownVerifyFactResult),
    Equality(Box<VerifyEqualityResult>),
    AtomicExceptEquality(Box<VerifyAtomicExceptEqualityFactResult>),
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
