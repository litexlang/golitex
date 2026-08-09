//! Litex-to-Lean bridge driven by verifier-produced To-Lean IR.

mod compilation_report;
mod rational_expression;
mod to_lean_pipeline;

pub use compilation_report::{
    ToLeanCompilationReport, ToLeanCompilationStatus, ToLeanUnsupported, ToLeanUnsupportedPhase,
};
pub use to_lean_pipeline::{
    emit_lean_from_ir, emit_lean_from_ir_with_report, to_lean, to_lean_from_source,
    to_lean_from_source_with_report, to_lean_with_report,
};
