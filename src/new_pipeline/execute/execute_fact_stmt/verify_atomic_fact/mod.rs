//! Verification stages for atomic facts.

pub mod result;
pub mod search_proof;
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
pub use search_proof::VerifyAtomicFactSearchProof;
