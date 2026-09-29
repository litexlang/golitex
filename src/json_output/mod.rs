//! Normal / Compact / Detailed JSON projection over Exec/Verify/Infer IR.
//!
//! Source of truth stays the result tree. This module only projects for humans / AI.
//! Default emit paths use `OutputDetail::Normal`. Detailed is implemented under
//! `project_detailed` (L2 local_env summary, T1 no search_trace). Compact is reserved.

pub mod emit;
pub mod explain;
pub mod helper;
pub mod project_detailed;
pub mod project_normal;

#[cfg(test)]
mod project_normal_tests;
#[cfg(test)]
mod project_detailed_tests;

pub use emit::{emit_run_detailed, emit_run_normal, stringify_normal};
pub use project_detailed::{project_run_detailed, project_stmt_detailed};
pub use project_normal::{project_run_normal, project_stmt_normal, OutputDetail};

use crate::knowledge_base::JsonValue;

pub type OutputJson = JsonValue;
