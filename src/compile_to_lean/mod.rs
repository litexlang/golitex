//! Litex-to-Lean compiler consuming verifier-produced Litex-to-Lean IR.

mod compilation_report;
#[cfg(test)]
pub(crate) mod lean_test_support;
mod shared_lean_library;
#[cfg(test)]
mod universal_examples_tests;
mod universal_pipeline;

pub use compilation_report::{
    LitexToLeanCompilationPhase, LitexToLeanCompilationReport, LitexToLeanCompilationStatus,
    LitexToLeanUnsupportedStatement,
};
pub use universal_pipeline::{
    compile_to_lean, compile_to_lean_from_source, compile_to_lean_from_source_with_report,
    compile_to_lean_with_report, emit_lean_from_litex_to_lean_ir,
    emit_lean_from_litex_to_lean_ir_with_report,
};
