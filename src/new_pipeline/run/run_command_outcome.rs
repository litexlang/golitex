use crate::new_pipeline::execute::ExecStmtResult;
use crate::new_pipeline::runtime::RuntimeError;
use std::path::PathBuf;

/// CLI command outcome. Run* carry payloads for later JSON; Help/Version are meta.
pub enum RunCommandOutcome {
    RunFile(RunFileResult),
    RunEval(RunEvalResult),
    RunRepo(RunRepoResult),
    Help(HelpResult),
    Version(VersionResult),
}

/// Session-stopping failure while a run was already under way.
/// Soft stmt Failed stays in `statement_results`, not here.
pub struct RunSessionError {
    pub cause: RuntimeError,
}

pub struct RunFileResult {
    pub path: PathBuf,
    pub all_stmts_succeeded: bool,
    pub statement_results: Vec<ExecStmtResult>,
    pub session_error: Option<RunSessionError>,
}

pub struct RunEvalResult {
    pub all_stmts_succeeded: bool,
    pub statement_results: Vec<ExecStmtResult>,
    pub session_error: Option<RunSessionError>,
}

pub struct RunRepoResult {
    pub path: PathBuf,
    pub all_stmts_succeeded: bool,
    pub files: Vec<RunFileResult>,
    pub session_error: Option<RunSessionError>,
}

pub struct HelpResult {
    pub entries: Vec<String>,
}

pub struct VersionResult {
    pub version: String,
}

/// Shared body of one source string run (`-e` / one `-f` file / one repo export).
pub struct RunLitexCodeResult {
    pub all_stmts_succeeded: bool,
    pub statement_results: Vec<ExecStmtResult>,
    pub session_error: Option<RunSessionError>,
}

impl RunSessionError {
    pub fn new(cause: RuntimeError) -> Self {
        Self { cause }
    }
}

impl RunLitexCodeResult {
    pub fn new(
        all_stmts_succeeded: bool,
        statement_results: Vec<ExecStmtResult>,
        session_error: Option<RunSessionError>,
    ) -> Self {
        Self {
            all_stmts_succeeded,
            statement_results,
            session_error,
        }
    }
}

impl RunFileResult {
    pub fn new(
        path: PathBuf,
        all_stmts_succeeded: bool,
        statement_results: Vec<ExecStmtResult>,
        session_error: Option<RunSessionError>,
    ) -> Self {
        Self {
            path,
            all_stmts_succeeded,
            statement_results,
            session_error,
        }
    }

    pub fn from_code_result(path: PathBuf, code_result: RunLitexCodeResult) -> Self {
        Self::new(
            path,
            code_result.all_stmts_succeeded,
            code_result.statement_results,
            code_result.session_error,
        )
    }

    pub fn process_failed(&self) -> bool {
        !self.all_stmts_succeeded
    }
}

impl RunEvalResult {
    pub fn new(
        all_stmts_succeeded: bool,
        statement_results: Vec<ExecStmtResult>,
        session_error: Option<RunSessionError>,
    ) -> Self {
        Self {
            all_stmts_succeeded,
            statement_results,
            session_error,
        }
    }

    pub fn from_code_result(code_result: RunLitexCodeResult) -> Self {
        Self::new(
            code_result.all_stmts_succeeded,
            code_result.statement_results,
            code_result.session_error,
        )
    }

    pub fn process_failed(&self) -> bool {
        !self.all_stmts_succeeded
    }
}

impl RunRepoResult {
    pub fn new(
        path: PathBuf,
        all_stmts_succeeded: bool,
        files: Vec<RunFileResult>,
        session_error: Option<RunSessionError>,
    ) -> Self {
        Self {
            path,
            all_stmts_succeeded,
            files,
            session_error,
        }
    }

    pub fn process_failed(&self) -> bool {
        !self.all_stmts_succeeded
    }
}

impl HelpResult {
    pub fn new(entries: Vec<String>) -> Self {
        Self { entries }
    }
}

impl VersionResult {
    pub fn new(version: impl Into<String>) -> Self {
        Self {
            version: version.into(),
        }
    }
}

impl RunCommandOutcome {
    pub fn process_failed(&self) -> bool {
        match self {
            Self::RunFile(r) => r.process_failed(),
            Self::RunEval(r) => r.process_failed(),
            Self::RunRepo(r) => r.process_failed(),
            Self::Help(_) | Self::Version(_) => false,
        }
    }
}
