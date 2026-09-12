//! Standalone execution-pipeline rewrite.
//!
//! Dual-track entry: set `LITEX_NEW_PIPELINE=1` to use `new_pipeline::run`
//! from the binary.  The legacy CLI remains the default when the variable is
//! unset.  Submodules own the new runtime, command dispatch, tokenization,
//! parse, execute, environment, and module-manager boundaries.

pub mod ast;
pub mod execute;
pub mod execution_environment;
pub mod module_manager;
pub mod parse;
pub mod run;
pub mod runtime;
pub mod tokenize;
