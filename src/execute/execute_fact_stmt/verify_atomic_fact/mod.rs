//! Verification stages for atomic facts.

pub(crate) mod helper;
mod known_subset_membership;

pub mod forall_match_result;
pub mod match_forall_conclusion_args;
pub mod prove_forall_instantiation_requirements;
pub mod result;
pub mod search_proof_by_known_forall_fact;
pub mod verify_atomic_except_equality;
pub mod verify_atomic_fact;
pub mod verify_equality;
pub mod verify_well_defined;
pub mod well_defined_result;

pub use verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition,
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, AtomicExceptEqualityFactSearchedProof,
    SearchProofByKnownStrategy, VerifyAtomicExceptEqualityFactFailed,
    VerifyAtomicExceptEqualityFactResult,
};
pub use verify_equality::SearchProofByKnownForallFact;
pub use verify_equality::{
    EqualFactSearchedProof, EqualFactSearchedProofByEquivalenceClass, EqualFactWellDefinedProof,
    FailToVerifyEqualFactWellDefinedResult, VerifyEqualFactWellDefinedResult, VerifyEqualityFailed,
    VerifyEqualityResult,
};
pub use well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    VerifyAtomicFactWellDefinedResult,
};

pub mod closed_calculation_proof;

pub mod search_structural_membership;
pub mod structural_membership_proof;
