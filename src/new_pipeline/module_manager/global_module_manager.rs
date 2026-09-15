//! Session/project-wide module owner for new_pipeline.

use super::export_file::ExportFileAndItsExecEnv;
use super::imported_module::ImportedModule;
use super::litex_config::LitexConfig;
use std::collections::HashMap;
use std::path::PathBuf;

/// Global mount table for one run.
///
/// - `imports` index = `mod_id`; global display name = `imports[mod_id].name`
/// - root is not an import slot
/// - resolve local alias via config path then `path_to_mod_id`
pub struct GlobalModuleManager {
    pub(crate) litex_config: LitexConfig,
    pub(crate) root_exports: Vec<ExportFileAndItsExecEnv>,
    pub(crate) imports: Vec<ImportedModule>,
    pub(crate) path_to_mod_id: HashMap<PathBuf, usize>,
}

impl GlobalModuleManager {
    pub fn new() -> Self {
        Self {
            litex_config: LitexConfig::new(),
            root_exports: Vec::new(),
            imports: Vec::new(),
            path_to_mod_id: HashMap::new(),
        }
    }

    pub fn new_with_root_config(litex_config: LitexConfig) -> Self {
        Self {
            litex_config,
            root_exports: Vec::new(),
            imports: Vec::new(),
            path_to_mod_id: HashMap::new(),
        }
    }

    pub fn litex_config(&self) -> &LitexConfig {
        &self.litex_config
    }

    pub fn root_exports(&self) -> &[ExportFileAndItsExecEnv] {
        &self.root_exports
    }

    pub fn imports(&self) -> &[ImportedModule] {
        &self.imports
    }

    pub fn path_to_mod_id(&self) -> &HashMap<PathBuf, usize> {
        &self.path_to_mod_id
    }

    pub fn record_root_export(&mut self, export: ExportFileAndItsExecEnv) {
        self.root_exports.push(export);
    }

    /// Register a module on the global table.
    ///
    /// Same `path` → silent merge, return existing `mod_id` (name unchanged).
    /// Same alias for a different path → error.
    pub fn record_import(
        &mut self,
        name: String,
        path: PathBuf,
        litex_config: LitexConfig,
    ) -> Result<usize, String> {
        if let Some(&mod_id) = self.path_to_mod_id.get(&path) {
            return Ok(mod_id);
        }
        if self.imports.iter().any(|m| m.name == name) {
            return Err(format!(
                "duplicate import alias `{name}` for a new path (alias already used by another module)"
            ));
        }
        let mod_id = self.imports.len();
        self.path_to_mod_id.insert(path.clone(), mod_id);
        self.imports
            .push(ImportedModule::new(name, path, litex_config));
        Ok(mod_id)
    }

    /// Append a finished export file to an already mounted import.
    pub fn record_imported_export(
        &mut self,
        mod_id: usize,
        export: ExportFileAndItsExecEnv,
    ) -> Result<(), String> {
        match self.imports.get_mut(mod_id) {
            Some(module) => {
                module.export_files_and_their_env.push(export);
                Ok(())
            }
            None => Err(format!("unknown mod_id {mod_id}")),
        }
    }

    pub fn global_name(&self, mod_id: usize) -> Result<&str, String> {
        self.imports
            .get(mod_id)
            .map(|m| m.name.as_str())
            .ok_or_else(|| format!("unknown mod_id {mod_id}"))
    }

    pub fn mod_id_for_path(&self, path: &PathBuf) -> Option<usize> {
        self.path_to_mod_id.get(path).copied()
    }
}
