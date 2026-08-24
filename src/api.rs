//! Curated public Rust API for embedding Litex.
//!
//! Prefer this module over importing the kernel's implementation modules or
//! the broad internal [`crate::prelude`]. Existing module paths remain
//! available for compatibility, but new embedders should start here.
//!
//! `run_source_code` executes inside an explicit source context:
//!
//! ```
//! use litex::api::{run_source_code, Runtime};
//!
//! let mut runtime = Runtime::new();
//! runtime.new_file_path_new_env_new_name_scope("embedded.lit");
//! let (results, error) = run_source_code("1 = 1", &mut runtime);
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
    run_file, run_file_with_project_context, run_file_with_project_context_and_trusted_prefix,
    run_repository, run_repository_with_output, run_repository_with_output_style, run_source_code,
    run_source_code_in_file, run_source_code_in_file_with_ok, run_source_code_with_options,
    FileRunOptions, RunOutputOptions, RunSourceFailureKind, RunSummary, SourceRunFailureKind,
    SourceRunOptions, SourceRunOutcome,
};

// Stable rendering entry points for embedding and machine-readable output.
pub use crate::output::{
    display_runtime_error_json, display_stmt_exec_result_json, display_stmt_result_json_v2,
};

// Litex-to-Lean entry points and their structured report types.
pub use crate::stmt_result_to_lean_compiler::{
    compile_litex_file_to_lean_file, compile_litex_markdown_code_blocks_to_lean_file,
    compile_litex_source_to_lean_source,
    compile_litex_source_to_stmt_result_to_lean_compilation_report,
    StmtResultToLeanCompilationPhase, StmtResultToLeanCompilationReport,
    StmtResultToLeanCompilationStatus, UnsupportedStmtResultToLeanCompilationItem,
};
