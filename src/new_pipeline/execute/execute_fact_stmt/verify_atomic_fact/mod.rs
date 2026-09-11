//! Verification stages for atomic facts.

pub mod result;
pub mod search_proof;
pub mod verify_equality;
pub mod verify_non_equational_atomic_fact;
pub mod well_defined;

pub use result::VerifyAtomicFactResult2;
pub use search_proof::VerifyAtomicFactSearchProof2;
