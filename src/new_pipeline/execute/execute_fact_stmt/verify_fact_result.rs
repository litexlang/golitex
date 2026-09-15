//! Top-level fact verification result.
//!
//! Mirrors `Fact` for compound shapes; atomic facts are flattened into
//! `Equality` / `AtomicExceptEquality` (no intermediate AtomicFact layer).
//!
//! Verify entry points return `RuntimeResult<VerifyFactResult>`:
//! - `Ok(FailToVerifyWellDefined)` / `Ok(FailToSearchProof)` = soft miss
//! - `Err` = real operational / invariant failure (SessionError)
//!
//! There is no fact-level exact-IR cite path: reuse known atomics / equality /
//! forall search instead. Object WD reuses `WellDefinedObjectMemory` via ByKnown.

use super::verify_atomic_fact::{VerifyAtomicExceptEqualityFactResult, VerifyEqualityResult};

pub enum VerifyFactResult {
    FailToVerifyWellDefined,
    FailToSearchProof,
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

// Composite search pipelines are not wired yet (always FailToSearchProof).
pub enum VerifyAndFactResult {}

pub enum VerifyChainFactResult {}

pub enum VerifyOrFactResult {}

pub enum VerifyExistFactResult {}

pub enum VerifyForallFactResult {}

pub enum VerifyForallFactWithIffResult {}

pub enum VerifyNotForallFactResult {}

impl VerifyFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(
            self,
            Self::FailToVerifyWellDefined | Self::FailToSearchProof
        )
    }
}
