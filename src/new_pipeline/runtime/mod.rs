//! Runtime-owned state and identity types for the new pipeline draft.

pub mod runtime;
pub mod runtime_ids;

pub use runtime::{ParseScope, Runtime, RuntimeOptions};
pub use runtime_ids::{AtomId, FactId, Id, PropAlgebraicPropertyId2, WellDefinednessId2};
