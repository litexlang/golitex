//! Litex-to-Lean bridge driven by verifier-produced To-Lean IR.

mod compilation_report;
#[cfg(test)]
mod examples_repository_tests;
mod helper;
mod rational_expression;
mod set_prelude;
mod to_lean_pipeline;
mod type_context;

pub use compilation_report::{
    ToLeanCompilationReport, ToLeanCompilationStatus, ToLeanUnsupported, ToLeanUnsupportedPhase,
};
pub use to_lean_pipeline::{
    emit_lean_from_ir, emit_lean_from_ir_with_report, to_lean, to_lean_from_source,
    to_lean_from_source_with_report, to_lean_with_report,
};
