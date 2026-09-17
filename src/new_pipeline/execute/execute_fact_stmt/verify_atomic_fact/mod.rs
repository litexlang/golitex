//! Verification stages for atomic facts.

pub mod result;
pub mod search_proof_by_known_forall_fact;
pub mod verify_atomic_except_equality;
pub mod verify_atomic_fact;
pub mod verify_equality;
pub mod verify_well_defined;
pub mod well_defined_result;

pub use result::SearchProofByKnownForallFact;
pub use verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition,
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, AtomicExceptEqualityFactSearchedProof,
    VerifyAtomicExceptEqualityFactFailed, VerifyAtomicExceptEqualityFactResult,
    VerifyAtomicExceptEqualityFactSuccess,
};
pub use verify_equality::{
    EqualFactSearchedProof, EqualFactSearchedProofByKnownEquality, VerifyEqualityFailed,
    VerifyEqualityResult, VerifyEqualitySuccess,
};
pub use well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    VerifyAtomicFactWellDefinedResult,
};
