//! Normal / Compact / Detailed JSON projection over Exec/Verify/Infer IR.
//!
//! Source of truth stays the result tree. This module only projects for humans / AI.
//! Default emit paths use `OutputDetail::Normal`. Compact is a thin success/fail
//! projection. Detailed is field-isomorphic IR projection under `project_detailed`
//! (`local_env` omitted).

pub mod emit;
pub mod explain;
pub mod helper;
pub mod json_keys;
pub mod project_compact;
pub mod project_detailed;
pub mod project_normal;
mod project_stmt_catalog;

#[cfg(test)]
mod acceptance_tests;
#[cfg(test)]
mod guarded_wd_repairs_tests;
#[cfg(test)]
mod local_rust_repairs_tests;
#[cfg(test)]
mod output_languages_tests;
#[cfg(test)]
mod project_compact_tests;
#[cfg(test)]
mod project_detailed_tests;
#[cfg(test)]
mod project_normal_tests;
#[cfg(test)]
mod rule_language_methods_tests;
#[cfg(test)]
mod template_failure_tests;

pub use emit::{emit_command_error, emit_run_compact, emit_run_detailed, emit_run_normal};
pub use project_compact::{project_run_compact, project_stmt_compact};
pub use project_detailed::{project_run_detailed, project_stmt_detailed};
pub use project_normal::{project_run_normal, project_stmt_normal, OutputDetail};

use crate::knowledge_base::JsonValue;

pub type OutputJson = JsonValue;
