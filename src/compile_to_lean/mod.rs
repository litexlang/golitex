//! Litex-to-Lean compiler consuming verifier-produced Litex-to-Lean IR.

mod compilation_report;
#[cfg(test)]
mod examples_repository_tests;
mod helper;
mod local_builtin_adapters;
#[cfg(test)]
mod local_builtin_catalog_tests;
mod pipeline;
mod rational_expression;
mod set_prelude;
mod type_context;

pub use compilation_report::{
    LitexToLeanCompilationPhase, LitexToLeanCompilationReport, LitexToLeanCompilationStatus,
    LitexToLeanUnsupportedStatement,
};
pub use pipeline::{
    compile_to_lean, compile_to_lean_from_source, compile_to_lean_from_source_with_report,
    compile_to_lean_with_report, emit_lean_from_litex_to_lean_ir,
    emit_lean_from_litex_to_lean_ir_with_report,
};
