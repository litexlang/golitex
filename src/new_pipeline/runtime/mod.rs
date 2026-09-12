//! Runtime-owned state and identity types for the new pipeline draft.

pub mod error;
pub mod runtime;
pub mod runtime_ids;

pub use error::{RuntimeError, RuntimeResult};
pub use runtime::{Ids, ParseScope, RealOrVirtualPath, Runtime};
pub use runtime_ids::{FactId, PropAlgebraicPropertyId, SymbolId, WellDefinednessId};
