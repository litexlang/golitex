//! Config-shaped module node for the new pipeline.

use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use std::path::PathBuf;

/// One module/config node. Completed environments are owned by the node that
/// executed them; imported modules are never merged into their importer.
pub struct ModuleManager {
    pub(crate) export_files_and_their_env: Vec<ExportFileAndItsExecEnv>,
    /// Mounted modules from `[import]` and `[import std]` (same representation).
    pub(crate) imports: Vec<ImportedModule>,
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

/// One mounted import: alias + resolved module path + that module's manager.
///
/// `[import]` and `[import std]` both become this after path resolution.
/// Aliases across both config sections share one namespace and must not clash.
pub struct ImportedModule {
    pub name: String,
    pub path: PathBuf,
    pub module_manager: ModuleManager,
}

impl ImportedModule {
    pub fn new(name: String, path: PathBuf, module_manager: ModuleManager) -> Self {
        Self {
            name,
            path,
            module_manager,
        }
    }
}

impl ModuleManager {
    pub fn new() -> Self {
        Self {
            export_files_and_their_env: Vec::new(),
            imports: Vec::new(),
        }
    }

    pub fn record_export_file(&mut self, export: ExportFileAndItsExecEnv) {
        self.export_files_and_their_env.push(export);
    }

    /// Record a mounted import. Fails if `import.name` is already used.
    pub fn record_import(&mut self, import: ImportedModule) -> Result<(), String> {
        if self.imports.iter().any(|existing| existing.name == import.name) {
            return Err(format!(
                "duplicate import alias `{}`: `[import]` and `[import std]` share one alias namespace",
                import.name
            ));
        }
        self.imports.push(import);
        Ok(())
    }

    pub fn exports(&self) -> &[ExportFileAndItsExecEnv] {
        &self.export_files_and_their_env
    }

    pub fn imports(&self) -> &[ImportedModule] {
        &self.imports
    }
}
