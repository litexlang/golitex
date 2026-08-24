mod compilation_report;
mod compiler_environment;
mod compiler_state;
mod file_compilation;
mod lean_compilation_types;
mod markdown_compilation;
mod registered_local_builtin_rule_identifiers_for_lean;
mod represent_litex_function_contracts_in_lean;
mod represent_litex_objects_in_lean;
mod source_compilation;

pub use compilation_report::{
    StmtResultToLeanCompilationPhase, StmtResultToLeanCompilationReport,
    StmtResultToLeanCompilationStatus, UnsupportedStmtResultToLeanCompilationItem,
};
pub use compiler_state::StmtResultToLeanCompiler;
pub use file_compilation::compile_litex_file_to_lean_file;
pub use markdown_compilation::compile_litex_markdown_code_blocks_to_lean_file;
pub use source_compilation::{
    compile_litex_source_to_lean_source,
    compile_litex_source_to_stmt_result_to_lean_compilation_report,
};
