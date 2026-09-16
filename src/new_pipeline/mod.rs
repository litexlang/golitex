//! Standalone execution-pipeline rewrite.
//!
//! Dual-track entry: set `LITEX_NEW_PIPELINE=1` to use `new_pipeline::run::launch`
//! from the binary.  The legacy CLI remains the default when the variable is
//! unset.  Submodules own the new runtime, command dispatch, tokenization,
//! parse, execute, environment, and module-manager boundaries.

/// Product display name for user-facing messages.
pub const LITEX: &str = "Litex";

pub mod ast;
pub mod launch_command;
pub mod display_and_ir;
pub mod exec_env;
pub mod execute;
pub mod instantiate;
pub mod module_manager;
pub mod parse;
pub mod run;
pub mod runtime;
pub mod store_fact_and_infer;
pub mod tokenize;
