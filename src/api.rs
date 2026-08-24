//! Curated public Rust API for embedding Litex.
//!
//! Prefer this module over importing the kernel's implementation modules or
//! the broad internal [`crate::prelude`].
//!
//! `execute_source` executes inside an explicit source context:
//!
//! ```
//! use litex::api::{execute_source, Runtime};
//!
//! let mut runtime = Runtime::new();
//! runtime.start_isolated_source("embedded.lit");
//! let (results, error) = execute_source("1 = 1", &mut runtime);
//! assert!(error.is_none());
//! assert_eq!(results.len(), 1);
//! ```

// Core execution model and result types.
pub use crate::common::output_language::OutputLanguage;
pub use crate::error::RuntimeError;
pub use crate::result::StmtResult;
pub use crate::runtime::{OutputStyle, Runtime, TrustedPrefixReport};

// Source, file, and repository execution entry points.
pub use crate::pipeline::{
    execute_source, run, PipelineStep, PipelineTrace, RunOptions, RunOutcome, RunRequest,
    RunSummary, RunTarget,
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
