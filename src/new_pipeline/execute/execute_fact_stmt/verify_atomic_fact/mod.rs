//! Verification stages for atomic facts.

pub mod result;
pub mod verify_atomic_fact;
pub mod verify_equality;
pub mod verify_non_equational_atomic_fact;
pub mod well_defined;

pub use result::{
    EqualFactSearchedProof, EqualFactSearchedProofByKnownAtomicFact,
    EqualFactSearchedProofByKnownForallFact, NonEquationalFactSearchedProof,
    NonEquationalFactSearchedProofByDefinition, NonEquationalFactSearchedProofByKnownAtomicFact,
    NonEquationalFactSearchedProofByKnownForallFact, VerifyAtomicFactResult,
    VerifyEqualityResult, VerifyNonEquationalFactResult,
};
