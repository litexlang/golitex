//! Top-level fact verification result.
//!
//! Mirrors `Fact` for compound shapes; atomic facts are flattened into
//! `Equality` / `AtomicExceptEquality` (no intermediate AtomicFact layer).
//!
//! Verify entry points return `RuntimeResult<VerifyFactResult>`:
//! - `Ok(Unknown)` = unable to prove (not a runtime error)
//! - `Err` = real operational / invariant failure

use super::cache_search_proof::CacheSearchProof;
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

// Composite stubs currently expose only exact FactIR ByCache; fuller search
// pipelines live in draft files until wired.
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
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }
}
