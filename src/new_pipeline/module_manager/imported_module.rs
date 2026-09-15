//! One globally mounted module (no nested manager).

use super::export_file::ExportFileAndItsExecEnv;
use super::litex_config::LitexConfig;
use std::path::PathBuf;

/// One entry in `GlobalModuleManager.imports`. Index in that vec is `mod_id`.
pub struct ImportedModule {
    /// Preferred global alias (first registration wins).
    pub name: String,
    /// Normalized module directory; dedup key via `path_to_mod_id`.
    pub path: PathBuf,
    pub litex_config: LitexConfig,
    pub export_files_and_their_env: Vec<ExportFileAndItsExecEnv>,
}

impl ImportedModule {
    pub fn new(name: String, path: PathBuf, litex_config: LitexConfig) -> Self {
        Self {
            name,
            path,
            litex_config,
            export_files_and_their_env: Vec::new(),
        }
    }
}
