//! Verification stages for atomic facts.

pub mod result;
pub mod search_proof_by_known_forall_fact;
pub mod verify_atomic_except_equality;
pub mod verify_atomic_fact;
pub mod verify_equality;

pub use result::{
    AtomicExceptEqualityFactSearchProofByDefinition,
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, AtomicExceptEqualityFactSearchedProof,
    EqualFactSearchedProof, EqualFactSearchedProofByKnownEquality, SearchProofByKnownForallFact,
    VerifyAtomicExceptEqualityFactResult, VerifyEqualityResult,
    WhyKnownAtomicParameterMatchesGiven,
};
