use crate::execute::ExecStmtResult;
use crate::runtime::RuntimeError;
use crate::runtime::RuntimeParseError;
use std::fmt;
use std::path::PathBuf;

/// CLI command outcome. Run* carry payloads for later JSON; Help/Version/Repl are meta.
pub enum RunCommandOutcome {
    RunFile(RunFileResult),
    RunEval(RunEvalResult),
    RunRepo(RunRepoResult),
    ExtractExecutableCode(ExtractExecutableCodeResult),
    CompileToLatex(CompileToLatexResult),
    CompileToLean(CompileToLeanResult),
    /// Interactive REPL: prints each step; no accumulated payload.
    RunRepl,
    Help(HelpResult),
    Version(VersionResult),
}

/// Session-stopping failure.
/// Soft stmt Failed stays in `statement_results` / `failed_statement_results`.
/// JSON exposes a failed statement with `statement_result: "rejected"` and
/// failure details. Top-level / hard stop is SessionError →
/// `session_terminated: true` plus structured `termination`.
/// `FailToImport`: mount / import / export soft-fail while loading a project (`-r` / `-f` / `-e` / REPL).
#[derive(Clone, Debug)]
pub enum RunSessionError {
    Runtime(RuntimeError),
    FailToImport(crate::prelude::ImportFailure),
}

impl fmt::Display for RunSessionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Runtime(error) => write!(f, "{error}"),
            Self::FailToImport(failure) => write!(f, "failed to import project: {failure}"),
        }
    }
}

/// Shared body of one source-string run (`-e` / `-f` / repo aggregate).
pub struct RunLitexCodeResult {
    pub success: bool,
    pub statement_results: Vec<ExecStmtResult>,
    /// Parsed source rendered before execution, aligned with statement_results.
    /// Empty for manually assembled result trees without source context.
    pub statement_texts: Vec<String>,
    /// Indices into `statement_results` of soft-Failed stmts.
    /// `None` when there is no soft Failed (JSON: null). `ExecStmtResult` is not
    /// Clone yet, so Rust stores indices; JSON can expand them to objects.
    pub failed_statement_results: Option<Vec<usize>>,
    /// A rejected source submission that did not produce an executable AST.
    /// The current submission stops, but its live Session can accept new input.
    pub input_error: Option<RunInputError>,
    pub session_error: Option<RunSessionError>,
    /// Pretty Normal JSON for this run (filled while Runtime is still alive).
    pub normal_json: Option<String>,
}

#[derive(Clone, Debug)]
pub struct RunInputError {
    pub statement: String,
    pub error: RuntimeParseError,
}

impl RunInputError {
    pub fn new(statement: String, error: RuntimeParseError) -> Self {
        Self { statement, error }
    }
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

pub struct ExtractExecutableCodeResult {
    pub json: String,
    pub success: bool,
}

/// Parse-only LaTeX artifact; success is conversion, not verification.
pub struct CompileToLatexResult {
    pub json: String,
    pub success: bool,
}

/// Complete Lean artifact. Soft verification failure is `success: false`, not SessionError.
pub struct CompileToLeanResult {
    pub source: String,
    pub success: bool,
}

impl CompileToLeanResult {
    pub fn new(source: String) -> Self {
        Self {
            source,
            success: true,
        }
    }

    pub fn soft_fail(message: String) -> Self {
        Self {
            source: message,
            success: false,
        }
    }

    pub fn process_failed(&self) -> bool {
        !self.success
    }
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
            statement_texts: Vec::new(),
            failed_statement_results,
            input_error: None,
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

    /// Fill `normal_json` with the initial batch plus later REPL turns.
    /// Does not change `success` / process exit; the snapshot `run_result`
    /// follows the merged statements.
    pub fn attach_normal_json_with_repl_turns(
        &mut self,
        runtime: &crate::runtime::Runtime,
        turns: &[RunLitexCodeResult],
        target: &str,
        path: Option<&std::path::Path>,
    ) {
        self.normal_json = Some(crate::json_output::emit_run_normal_with_turns(
            self, turns, runtime, target, path,
        ));
    }

    /// Preserve the batch's already-rendered citations after a REPL abort has
    /// discarded the live environment. Only the run envelope changes.
    pub fn attach_session_error(
        &mut self,
        runtime: &crate::runtime::Runtime,
        target: &str,
        path: Option<&std::path::Path>,
        error: RunSessionError,
    ) {
        self.success = false;
        self.session_error = Some(error);
        if let Some(crate::knowledge_base::JsonValue::Object(mut fields)) = self
            .normal_json
            .as_deref()
            .and_then(|json| crate::knowledge_base::JsonValue::parse(json).ok())
        {
            let language = runtime.launch_command.output_language();
            let key = |name| crate::json_output::json_keys::localize_key(name, language);
            fields.insert(
                key("run_result"),
                crate::knowledge_base::JsonValue::String("failure".into()),
            );
            fields.insert(
                key("session_terminated"),
                crate::knowledge_base::JsonValue::Bool(true),
            );
            fields.insert(
                key("termination"),
                crate::json_output::helper::session_termination_value(
                    self.session_error
                        .as_ref()
                        .expect("session error was just set"),
                    language,
                ),
            );
            self.normal_json =
                Some(crate::knowledge_base::JsonValue::Object(fields).stringify_pretty());
        } else {
            self.attach_normal_json(runtime, target, path);
        }
    }
}

impl RunFileResult {
    pub fn new(path: PathBuf, run: RunLitexCodeResult) -> Self {
        Self { path, run }
    }

    pub fn process_failed(&self) -> bool {
        self.run.process_failed()
    }

    /// A rejected prerequisite prevents mounting the requested project context.
    pub(crate) fn mount_error(&self) -> RunSessionError {
        if let Some(error) = &self.run.session_error {
            return error.clone();
        }
        if let Some(input) = &self.run.input_error {
            return RunSessionError::Runtime(RuntimeError::ParseError(input.error.clone()));
        }
        RunSessionError::FailToImport(crate::prelude::ImportFailure::rejected_export(self))
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
            statement_texts: Vec::new(),
            failed_statement_results: None,
            input_error: None,
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

impl ExtractExecutableCodeResult {
    pub fn new(json: String, success: bool) -> Self {
        Self { json, success }
    }

    pub fn process_failed(&self) -> bool {
        !self.success
    }
}

impl CompileToLatexResult {
    pub fn new(json: String, success: bool) -> Self {
        Self { json, success }
    }

    pub fn process_failed(&self) -> bool {
        !self.success
    }
}

impl RunCommandOutcome {
    pub fn process_failed(&self) -> bool {
        match self {
            Self::RunFile(r) => r.process_failed(),
            Self::RunEval(r) => r.process_failed(),
            Self::RunRepo(r) => r.process_failed(),
            Self::ExtractExecutableCode(r) => r.process_failed(),
            Self::CompileToLatex(r) => r.process_failed(),
            Self::CompileToLean(r) => r.process_failed(),
            Self::RunRepl | Self::Help(_) | Self::Version(_) => false,
        }
    }

    pub fn normal_json(&self) -> Option<&str> {
        match self {
            Self::RunFile(r) => r.run.normal_json.as_deref(),
            Self::RunEval(r) => r.run.normal_json.as_deref(),
            Self::RunRepo(r) => r.run.normal_json.as_deref(),
            Self::ExtractExecutableCode(r) => Some(r.json.as_str()),
            Self::CompileToLatex(r) => Some(r.json.as_str()),
            Self::CompileToLean(_) | Self::RunRepl | Self::Help(_) | Self::Version(_) => None,
        }
    }
}
