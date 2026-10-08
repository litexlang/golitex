//! Litex language kernel.

/// Product display name for user-facing messages.
pub const LITEX: &str = "Litex";

pub mod ast;
pub mod builtin_theorem;
pub mod compile_to_latex;
pub mod compile_to_lean;
pub mod launch_command;
#[cfg(test)]
mod launch_command_tests;
pub mod display_and_ir;
pub mod exec_env;
pub mod execute;
pub mod extract_executable_code;
pub mod instantiate;
pub mod json_output;
pub mod knowledge_base;
pub mod module_manager;
pub mod parse;
pub(crate) mod prelude;
pub mod rational_expression;
pub mod run;
pub mod run_module;
pub mod runtime;
pub mod store_fact_and_infer;
pub mod tokenize;
