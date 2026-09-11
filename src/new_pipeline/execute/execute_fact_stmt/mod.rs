//! Staging boundary for the refactored verifier.
//!
//! The running `Runtime` still uses [`crate::verification`].  This namespace
//! owns the new verifier's foundational types while its Result and pipeline
//! modules are migrated incrementally.  Keeping the boundary explicit lets
//! the new implementation grow without creating two active implementations of
//! the same `Runtime` methods.

pub mod verify_state;
pub mod verify_atomic_fact;
pub mod cache_search_proof;
pub mod verify_fact_result;

pub use crate::environment::Environment;
pub use crate::fact::{
    AndFact, AtomicFact, ChainFact, EqualFact, ExistFact, Fact, ForallFact, ForallFactWithIff,
    NotForallFact, OrFact, PlainExistFact,
};
pub use crate::runtime::Runtime;
pub use verify_state::VerifyState2;
