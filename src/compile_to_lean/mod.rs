//! Litex-to-Lean compiler building IR from verifier results and emitting Lean.

mod compilation_report;
mod file;
mod ir_builder;
#[cfg(test)]
pub(crate) mod lean_test_support;
mod ledger;
mod shared_lean_library;
#[cfg(test)]
mod universal_examples_tests;
mod universal_pipeline;

pub use compilation_report::{
    LitexToLeanCompilationPhase, LitexToLeanCompilationReport, LitexToLeanCompilationStatus,
    LitexToLeanUnsupportedStatement,
};
pub(crate) use file::compile_litex_file_to_lean;
pub use ir_builder::LitexToLeanCompiler;
pub(crate) use ledger::compile_markdown_ledger_file_to_lean;
pub use universal_pipeline::{
    capture_litex_to_lean_ir_from_source, compile_to_lean, compile_to_lean_from_source,
    compile_to_lean_from_source_with_report, compile_to_lean_with_report,
    emit_lean_from_litex_to_lean_ir, emit_lean_from_litex_to_lean_ir_with_report,
};
