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
pub use runtime_ids::{FactId, PropAlgebraicPropertyId};
pub use verify_state::VerifyState;

/// A fact statement is the `Fact` payload carried by `Stmt::Fact`.
///
/// Keep this name in the verifier layer so Result fields can describe their
/// statement role while still using the runtime's canonical fact node.
pub type FactStmt = Fact;
