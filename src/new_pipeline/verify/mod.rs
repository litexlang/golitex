//! Staging boundary for the refactored verifier.
//!
//! The running `Runtime` still uses [`crate::verification`].  This namespace
//! owns the new verifier's foundational types while its Result and pipeline
//! modules are migrated incrementally.  Keeping the boundary explicit lets
//! the new implementation grow without creating two active implementations of
//! the same `Runtime` methods.

pub mod runtime_ids;
pub mod verify_state;

pub use crate::environment::Environment;
pub use crate::fact::{
    AndFact, AtomicFact, ChainFact, EqualFact, ExistFact, Fact, ForallFact, ForallFactWithIff,
    NotForallFact, OrFact, PlainExistFact,
};
pub use crate::runtime::Runtime;
pub use runtime_ids::{FactId, PropAlgebraicPropertyId2, WellDefinednessId2};
pub use verify_state::VerifyState2;

