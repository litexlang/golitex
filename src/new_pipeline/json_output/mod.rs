//! Normal / Compact / Detailed JSON projection over Exec/Verify/Infer IR.
//!
//! Source of truth stays the result tree. This module only projects for humans / AI.
//! Today every emit path uses `OutputDetail::Normal`. Compact and Detailed are
//! reserved until their contracts are designed.

pub mod emit;
pub mod helper;
pub mod project_normal;

#[cfg(test)]
mod project_normal_tests;

pub use emit::{emit_run_normal, stringify_normal};
pub use project_normal::{project_run_normal, project_stmt_normal, OutputDetail};

use crate::new_pipeline::knowledge_base::JsonValue;

pub type OutputJson = JsonValue;
