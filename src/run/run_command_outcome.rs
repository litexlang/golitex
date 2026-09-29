use crate::execute::ExecStmtResult;
use crate::runtime::RuntimeError;
use std::path::PathBuf;

/// CLI command outcome. Run* carry payloads for later JSON; Help/Version/Repl are meta.
pub enum RunCommandOutcome {
    RunFile(RunFileResult),
    RunEval(RunEvalResult),
    RunRepo(RunRepoResult),
    Extract(ExtractResult),
    /// Interactive REPL: prints each step; no accumulated payload.
    RunRepl,
    Help(HelpResult),
    Version(VersionResult),
}

/// Session-stopping failure.
/// Soft stmt Failed stays in `statement_results` / `failed_statement_results`.
/// JSON maps Failed → `"error"` (presentation only; Rust stays Failed, not Error).
/// Top-level / hard stop is SessionError → `"session_error"`.
/// `FailToImport`: mount / import / export soft-fail while loading a project (`-r` / `-f` / `-e` / REPL).
#[derive(Clone, Debug)]
pub enum RunSessionError {
    Runtime(RuntimeError),
    FailToImport,
}

/// Shared body of one source-string run (`-e` / `-f` / repo aggregate).
pub struct RunLitexCodeResult {
    pub success: bool,
    pub statement_results: Vec<ExecStmtResult>,
    /// Indices into `statement_results` of soft-Failed stmts.
    /// `None` when there is no soft Failed (JSON: null). `ExecStmtResult` is not
    /// Clone yet, so Rust stores indices; JSON can expand them to objects.
    pub failed_statement_results: Option<Vec<usize>>,
    pub session_error: Option<RunSessionError>,
    /// Pretty Normal JSON for this run (filled while Runtime is still alive).
    pub normal_json: Option<String>,
}

pub struct RunFileResult {
    pub path: PathBuf,
    pub run: RunLitexCodeResult,
}

pub struct RunEvalResult {
    pub run: RunLitexCodeResult,
}

pub struct RunRepoResult {
    pub path: PathBuf,
    pub run: RunLitexCodeResult,
    pub files: Vec<RunFileResult>,
}

pub struct HelpResult {
    pub entries: Vec<String>,
}

pub struct VersionResult {
    pub version: String,
}

pub struct ExtractResult {
    pub json: String,
    pub ok: bool,
}

fn failed_indices(statement_results: &[ExecStmtResult]) -> Option<Vec<usize>> {
    let indices: Vec<usize> = statement_results
        .iter()
        .enumerate()
        .filter(|(_, result)| result.is_failed())
        .map(|(index, _)| index)
        .collect();
    if indices.is_empty() {
        None
    } else {
        Some(indices)
    }
}

fn success_flag(
    statement_results: &[ExecStmtResult],
    session_error: &Option<RunSessionError>,
) -> bool {
    session_error.is_none() && statement_results.iter().all(|result| !result.is_failed())
}

impl RunLitexCodeResult {
    pub fn new(
        statement_results: Vec<ExecStmtResult>,
        session_error: Option<RunSessionError>,
    ) -> Self {
        let failed_statement_results = failed_indices(&statement_results);
        let success = success_flag(&statement_results, &session_error);
        Self {
            success,
            statement_results,
            failed_statement_results,
            session_error,
            normal_json: None,
        }
    }

    pub fn process_failed(&self) -> bool {
        !self.success
    }

    /// Fill `normal_json` while the Runtime still holds cited facts.
    pub fn attach_normal_json(
        &mut self,
        runtime: &crate::runtime::Runtime,
        target: &str,
        path: Option<&std::path::Path>,
    ) {
        self.normal_json = Some(crate::json_output::emit_run_normal(
            self, runtime, target, path,
        ));
    }
}

impl RunFileResult {
    pub fn new(path: PathBuf, run: RunLitexCodeResult) -> Self {
        Self { path, run }
    }

    pub fn process_failed(&self) -> bool {
        self.run.process_failed()
    }
}

impl RunEvalResult {
    pub fn new(run: RunLitexCodeResult) -> Self {
        Self { run }
    }

    pub fn process_failed(&self) -> bool {
        self.run.process_failed()
    }
}

impl RunRepoResult {
    pub fn new(
        path: PathBuf,
        files: Vec<RunFileResult>,
        session_error: Option<RunSessionError>,
    ) -> Self {
        let success = session_error.is_none() && files.iter().all(|file| file.run.success);
        let run = RunLitexCodeResult {
            success,
            statement_results: Vec::new(),
            failed_statement_results: None,
            session_error,
            normal_json: None,
        };
        Self { path, run, files }
    }

    pub fn process_failed(&self) -> bool {
        self.run.process_failed()
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

impl ExtractResult {
    pub fn new(json: String, ok: bool) -> Self {
        Self { json, ok }
    }

    pub fn process_failed(&self) -> bool {
        !self.ok
    }
}

impl RunCommandOutcome {
    pub fn process_failed(&self) -> bool {
        match self {
            Self::RunFile(r) => r.process_failed(),
            Self::RunEval(r) => r.process_failed(),
            Self::RunRepo(r) => r.process_failed(),
            Self::Extract(r) => r.process_failed(),
            Self::RunRepl | Self::Help(_) | Self::Version(_) => false,
        }
    }

    pub fn normal_json(&self) -> Option<&str> {
        match self {
            Self::RunFile(r) => r.run.normal_json.as_deref(),
            Self::RunEval(r) => r.run.normal_json.as_deref(),
            Self::RunRepo(r) => r.run.normal_json.as_deref(),
            Self::Extract(r) => Some(r.json.as_str()),
            Self::RunRepl | Self::Help(_) | Self::Version(_) => None,
        }
    }
}
