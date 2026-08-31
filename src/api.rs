//! Curated public Rust API for embedding Litex.
//!
//! Prefer this module over importing the kernel's implementation modules or
//! the broad internal [`crate::prelude`].
//!
//! `Runtime::execute_source` executes inside an explicit source context:
//!
//! ```
//! use litex::api::Runtime;
//!
//! let mut runtime = Runtime::default();
//! runtime.start_isolated_source("embedded.lit");
//! let (results, error) = runtime.execute_source("1 = 1").into_parts();
//! assert!(error.is_none());
//! assert_eq!(results.len(), 1);
//! ```

// Core execution model and result types.
pub use crate::error::RuntimeError;
pub use crate::output::{language::OutputLanguage, style::OutputStyle};
pub use crate::result::StmtResult;
pub use crate::runtime::{ExecutionOption, RunOption, RunOptions, Runtime, SummaryOption};

// Source, file, and repository execution entry points.
pub use crate::pipeline::{
    run_code, run_file, run_repository, FileRunMode, RunOutcome, RunSummary, RunTarget,
    RunTargetKind, SourceRunOutcome,
};

// Stable rendering entry points for embedding and machine-readable output.
pub use crate::output::{
    display_runtime_error_json, display_stmt_exec_result_json, display_stmt_result_json_v2,
};

// Litex-to-Lean entry points and their structured report types.
pub use crate::stmt_result_to_lean_compiler::{
    compile_litex_file_to_lean_file, compile_litex_markdown_code_blocks_to_lean_file,
    compile_litex_source_to_lean_compilation_report, compile_litex_source_to_lean_source,
    StmtResultToLeanCompilationPhase, StmtResultToLeanCompilationReport,
    StmtResultToLeanCompilationStatus, UnsupportedStmtResultToLeanCompilationItem,
};
