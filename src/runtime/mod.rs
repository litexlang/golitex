//! Runtime core data model and identity types for the new pipeline.
//!
//! `Runtime` is process-wide session state (stacks, ids, modules).  Per-scope
//! stores live in `ExecEnv` on `execution_environments_stack`.
//!
//! Symbol identity premise: `../identifier_identity.md`
//! (plain occurrences carry IdentifierId; qualified atoms do not).

pub mod error;
pub mod internal_names;
#[cfg(test)]
mod internal_names_tests;
pub mod real_or_virtual_path;
pub mod code_source;
pub mod runtime;
pub mod runtime_ids;

pub use code_source::CodeSource;
pub use error::{RuntimeError, RuntimeParseError, RuntimeResult};
pub use real_or_virtual_path::RealOrVirtualPath;
pub use runtime::{GlobalIds, ParseScope, Runtime};
pub use runtime_ids::{FactId, IdentifierId, PropRewritePropertyId, WellDefinednessId};
