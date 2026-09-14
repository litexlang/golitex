//! Verification stages for atomic facts.

pub mod result;
pub mod verify_atomic_fact;
pub mod verify_equality;
pub mod verify_atomic_except_equality;
pub mod well_defined;

pub use result::{
    AtomicExceptEqualityFactSearchProofByDefinition,
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
    AtomicExceptEqualityFactSearchProofByKnownForallFact, AtomicExceptEqualityFactSearchedProof,
    EqualFactSearchedProof, EqualFactSearchedProofByKnownEquality,
    EqualFactSearchedProofByKnownForallFact, VerifyAtomicExceptEqualityFactResult,
    VerifyEqualityResult,
};
