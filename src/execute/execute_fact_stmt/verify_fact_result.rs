//! Top-level fact verification result.
//!
//! Mirrors `Fact` for compound shapes; atomic facts are flattened into
//! `Equality` / `AtomicExceptEquality` (no intermediate AtomicFact layer).
//! Soft miss lives inside each branch `VerifyXXXResult` as `Failed`, not here.
//!
//! Part of the Exec/Verify/Infer evidence IR: human/AI JSON and Lean replay
//! share the winning route (see `execute/README.md` Result shape). Keep
//! `searched_proof` as the named route only; not search noise, not pass/fail-only.
//!
//! Verify entry points return `RuntimeResult<VerifyFactResult>`:
//! - `Ok(branch(Failed(...)))` = soft miss (WD or search)
//! - `Err` = real operational / invariant failure (SessionError)
//!
//! There is no fact-level exact-IR cite path: reuse known atomics / equality /
//! forall search instead. Object WD reuses `WellDefinedObjectMemory` via ByKnown.

use super::verify_and_fact::{VerifyAndFactFailed, VerifyAndFactResult};
use super::verify_atomic_fact::{VerifyAtomicExceptEqualityFactResult, VerifyEqualityResult};
use super::verify_chain_fact::{VerifyChainFactFailed, VerifyChainFactResult};
use super::verify_exist_shaped_fact::{
    VerifyExistShapedFactFailed, VerifyExistShapedFactResult, VerifyExistUniqueFactResult,
    VerifyNotExistFactResult, VerifyPlainExistFactResult,
};
use super::verify_forall_fact::{VerifyForallFactFailed, VerifyForallFactResult};
use super::verify_forall_fact_with_iff::VerifyForallFactWithIffResult;
use super::verify_not_forall_fact::VerifyNotForallFactResult;
use super::verify_or_fact::{VerifyOrFactFailed, VerifyOrFactResult};

pub enum VerifyFactResult {
    Equality(Box<VerifyEqualityResult>),
    AtomicExceptEquality(Box<VerifyAtomicExceptEqualityFactResult>),
    AndFact(Box<VerifyAndFactResult>),
    ChainFact(Box<VerifyChainFactResult>),
    OrFact(Box<VerifyOrFactResult>),
    ExistShapedFact(Box<VerifyExistShapedFactResult>),
    ForallFact(Box<VerifyForallFactResult>),
    ForallFactWithIff(Box<VerifyForallFactWithIffResult>),
    NotForall(Box<VerifyNotForallFactResult>),
}

impl VerifyFactResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Equality(r) => r.is_failed(),
            Self::AtomicExceptEquality(r) => r.is_failed(),
            Self::AndFact(r) => r.is_failed(),
            Self::ChainFact(r) => r.is_failed(),
            Self::OrFact(r) => r.is_failed(),
            Self::ExistShapedFact(r) => r.is_failed(),
            Self::ForallFact(r) => r.is_failed(),
            Self::ForallFactWithIff(r) => r.is_failed(),
            Self::NotForall(r) => r.is_failed(),
        }
    }

    // True when this soft miss is a WD failure (possibly nested under And/Chain/…).
    pub fn is_wd_failed(&self) -> bool {
        match self {
            Self::Equality(r) => matches!(
                r.as_ref(),
                VerifyEqualityResult::Failed(
                    super::verify_atomic_fact::VerifyEqualityFailed::FailToVerifyWellDefined(_)
                )
            ),
            Self::AtomicExceptEquality(r) => matches!(
                r.as_ref(),
                VerifyAtomicExceptEqualityFactResult::Failed(
                    super::verify_atomic_fact::VerifyAtomicExceptEqualityFactFailed::FailToVerifyWellDefined(
                        _
                    )
                )
            ),
            Self::AndFact(r) => matches!(
                r.as_ref(),
                VerifyAndFactResult::Failed(VerifyAndFactFailed::FailToVerifyWellDefined { .. })
            ),
            Self::ChainFact(r) => matches!(
                r.as_ref(),
                VerifyChainFactResult::Failed(VerifyChainFactFailed::FailToVerifyWellDefined { .. })
            ),
            Self::OrFact(r) => matches!(
                r.as_ref(),
                VerifyOrFactResult::Failed(VerifyOrFactFailed::FailToVerifyWellDefined(_))
            ),
            Self::ExistShapedFact(r) => match r.as_ref() {
                VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Failed(
                    VerifyExistShapedFactFailed::FailToVerifyWellDefined(_),
                ))
                | VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(
                    VerifyExistShapedFactFailed::FailToVerifyWellDefined(_),
                ))
                | VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Failed(
                    VerifyExistShapedFactFailed::FailToVerifyWellDefined(_),
                )) => true,
                _ => false,
            },
            Self::ForallFact(r) => matches!(
                r.as_ref(),
                VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(_))
            ),
            Self::ForallFactWithIff(_) | Self::NotForall(_) => false,
        }
    }
}
