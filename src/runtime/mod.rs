//! Runtime core data model and identity types.
//!
//! `Runtime` is process-wide session state (stacks, ids, modules).  Per-scope
//! stores live in `ExecEnv` on `execution_environments_stack`.
//!
//! Symbol identity premise: `../identifier_identity.md`
//! (plain occurrences carry IdentifierId; qualified atoms do not).

pub mod code_source;
#[cfg(test)]
mod code_source_tests;
pub mod error;
#[cfg(test)]
mod internal_error_tests;
pub mod internal_names;
#[cfg(test)]
mod internal_names_tests;
mod parse_scope_transaction;
pub mod runtime;
pub mod runtime_ids;

pub use code_source::CodeSource;
pub use error::{RuntimeError, RuntimeParseError, RuntimeResult};
pub use runtime::{GlobalIds, ParseScope, Runtime};
pub use runtime_ids::{FactId, IdentifierId, PropRewritePropertyId, WellDefinednessId};
