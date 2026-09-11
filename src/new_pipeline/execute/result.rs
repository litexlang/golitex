use crate::new_pipeline::parse::ParsedStatement;
use crate::new_pipeline::runtime::{PipelineError, PipelineResult, RunTarget, Runtime};

/// Results collected for one successfully executed source file.
///
/// The file's persistent top-level `ExecEnv` is owned by `ModuleManager`; it
/// is not duplicated here.  Statement results may retain child environments
/// when a particular statement needs to expose local proof state.
pub struct FileRunResult {
    pub name: String,
    pub path: std::path::PathBuf,
    pub statement_results: Vec<ExecStmtResult2>,
}

/// Result returned by a top-level `run_litex_code` invocation.
pub struct RunResult {
    pub target: RunTarget,
    pub files: Vec<FileRunResult>,
}

/// Result of executing one parsed statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecStmtResult2 {
    /// Placeholder until statement-specific verified Result variants are
    /// migrated into the new pipeline.
    Placeholder { line: usize },
}

impl Runtime {
    /// Verified statement execution boundary.
    pub fn exec_stmt(&mut self, stmt: &ParsedStatement) -> PipelineResult<ExecStmtResult2> {
        if stmt.tokens.is_empty() {
            return Err(PipelineError::Invariant(format!(
                "executor received an empty statement at line {}",
                stmt.line
            )));
        }

        // The real implementation will dispatch here to:
        //   verify_well_defined -> search proof -> store fact/infer -> Result.
        Ok(ExecStmtResult2::Placeholder { line: stmt.line })
    }
}
