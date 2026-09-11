//! Runtime-owned state and identity types for the new pipeline draft.

pub mod error;
pub mod runtime;
pub mod runtime_ids;

pub use error::{PipelineError, PipelineResult};
pub use runtime::{Ids, ParseScope, RealOrVirtualPath, Runtime};
pub use runtime_ids::{
    AtomId, FactId, PropAlgebraicPropertyId, SymbolId, WellDefinednessId,
};
