//! Verification stages for atomic facts.

pub mod result;
pub mod verify_atomic_fact;
pub mod verify_equality;
pub mod verify_atomic_except_equality;
pub mod well_defined;

pub use result::{
    EqualFactSearchedProof, EqualFactSearchedProofByKnownAtomicFact,
    EqualFactSearchedProofByKnownForallFact, AtomicExceptEqualityFactSearchProofByDefinition,
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, AtomicExceptEqualityFactSearchProofByKnownForallFact,
    AtomicExceptEqualityFactSearchedProof, VerifyAtomicFactResult, VerifyEqualityResult,
    VerifyAtomicExceptEqualityFactResult,
};
