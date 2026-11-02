//! Original file executions retained for module-aware Lean replay.
use crate::run::{RunFileResult, RunLitexCodeResult, RunSessionError};
use crate::runtime::{CodeSource, Runtime};
use std::path::PathBuf;

/// One actual source execution; publication identity is captured before parsing.
pub struct LeanSourceFile {
    pub source: CodeSource,
    pub run: RunLitexCodeResult,
}

/// Dependency/export execution order, ending at the requested target.
pub struct LeanSourceClosure {
    pub files: Vec<LeanSourceFile>,
    pub target_file: usize,
}

pub struct LoadedLeanSource {
    pub closure: LeanSourceClosure,
    pub runtime: Runtime,
}

pub enum LoadLeanSourceResult {
    Success(LoadedLeanSource),
    Failed(LoadLeanSourceFailure),
}

pub enum LoadLeanSourceFailure {
    Import {
        path: PathBuf,
        error: RunSessionError,
    },
    File(RunFileResult),
}
