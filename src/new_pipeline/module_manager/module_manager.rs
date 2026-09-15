//! Config-shaped module node for the new pipeline.

use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use std::path::PathBuf;

/// One module/config node. Completed environments are owned by the node that
/// executed them; imported modules are never merged into their importer.
pub struct ModuleManager {
    pub(crate) export_files_and_their_env: Vec<ExportFileAndItsExecEnv>,
    pub(crate) import_repos: Vec<ModuleManager>,
    pub(crate) import_std: Vec<ImportStdRepoAndItsExecEnv>,
}

/// A completed export file and its top-level execution environment.
pub struct ExportFileAndItsExecEnv {
    pub name: String,
    pub path: PathBuf,
    pub exec_env: Box<ExecEnv>,
}

impl ExportFileAndItsExecEnv {
    pub fn new(name: String, path: PathBuf, exec_env: Box<ExecEnv>) -> Self {
        Self {
            name,
            path,
            exec_env,
        }
    }
}

/// A completed standard-library source environment.
pub struct ImportStdRepoAndItsExecEnv {
    pub name: String,
    pub exec_env: Box<ExecEnv>,
}

impl ModuleManager {
    pub fn new() -> Self {
        Self {
            export_files_and_their_env: Vec::new(),
            import_repos: Vec::new(),
            import_std: Vec::new(),
        }
    }

    pub fn record_export_file(&mut self, export: ExportFileAndItsExecEnv) {
        self.export_files_and_their_env.push(export);
    }

    pub fn record_import_std(&mut self, import: ImportStdRepoAndItsExecEnv) {
        self.import_std.push(import);
    }

    pub fn record_import_repo(&mut self, module: ModuleManager) {
        self.import_repos.push(module);
    }

    pub fn exports(&self) -> &[ExportFileAndItsExecEnv] {
        &self.export_files_and_their_env
    }

    pub fn imported_repositories(&self) -> &[ModuleManager] {
        &self.import_repos
    }

    pub fn imported_std(&self) -> &[ImportStdRepoAndItsExecEnv] {
        &self.import_std
    }
}
