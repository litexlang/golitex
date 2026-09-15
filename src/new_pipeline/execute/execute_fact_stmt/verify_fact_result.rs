//! Top-level fact verification result.
//!
//! Mirrors `Fact` for compound shapes; atomic facts are flattened into
//! `Equality` / `AtomicExceptEquality` (no intermediate AtomicFact layer).
//!
//! Verify entry points return `RuntimeResult<VerifyFactResult>`:
//! - `Ok(FailToVerifyWellDefined)` / `Ok(FailToSearchProof)` = soft miss
//! - `Err` = real operational / invariant failure (SessionError)

use super::cache_search_proof::CacheSearchProof;
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

// Composite stubs currently expose only exact FactIR ByCache; fuller search
// pipelines are not wired yet.
pub enum VerifyAndFactResult {
    ByCache(CacheSearchProof),
}

pub enum VerifyChainFactResult {
    ByCache(CacheSearchProof),
}

pub enum VerifyOrFactResult {
    ByCache(CacheSearchProof),
}

pub enum VerifyExistFactResult {
    ByCache(CacheSearchProof),
}

pub enum VerifyForallFactResult {
    ByCache(CacheSearchProof),
}

pub enum VerifyForallFactWithIffResult {
    ByCache(CacheSearchProof),
}

pub enum VerifyNotForallFactResult {
    ByCache(CacheSearchProof),
}

impl VerifyFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(
            self,
            Self::FailToVerifyWellDefined | Self::FailToSearchProof
        )
    }
}
