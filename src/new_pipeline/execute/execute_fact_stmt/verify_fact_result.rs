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
use super::verify_well_defined::FactWellDefinedProof;
use crate::new_pipeline::ast::fact::ForallFact;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

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

// Composite search pipelines not yet wired (except forall local proof).
pub enum VerifyAndFactResult {}

pub enum VerifyChainFactResult {}

pub enum VerifyOrFactResult {}

pub enum VerifyExistFactResult {}

pub enum VerifyForallFactWithIffResult {}

pub enum VerifyNotForallFactResult {}

// forall local-proof pipeline (field order = stage order).
// `local_env` is the closed binder scope; it is not merged into the parent.
// The parent stores the whole forall only after this verify succeeds.
pub struct VerifyForallFactResult {
    pub fact: ForallFact,
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub proved_then_facts: Vec<ProveAndStoreThenFactResult>,
    pub local_env: Box<ExecEnv>,
}

// Dom: assume (WD + store), do not prove truth.
pub struct AssumeDomFactResult {
    pub well_defined: FactWellDefinedProof,
    pub store_and_infer: StoreFactAndInferResult,
}

// Then: prove, then local-store (option 2).
pub struct ProveAndStoreThenFactResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer: StoreFactAndInferResult,
}

impl VerifyFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(
            self,
            Self::FailToVerifyWellDefined | Self::FailToSearchProof
        )
    }
}
