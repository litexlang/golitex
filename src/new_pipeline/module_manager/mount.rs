//! Mount / readiness helpers on the global table (no file execution).

use super::global_module_manager::GlobalModuleManager;
use super::litex_config::LitexConfig;
use std::path::PathBuf;

impl GlobalModuleManager {
    pub fn set_root_config(&mut self, litex_config: LitexConfig) {
        self.litex_config = litex_config;
    }

    /// Every import path in `config` must already be on `path_to_mod_id`.
    pub fn ensure_imports_ready(&self, config: &LitexConfig) -> Result<(), String> {
        for row in &config.imports {
            if !self.path_to_mod_id.contains_key(&row.path) {
                return Err(format!(
                    "import `{}` path `{}` is not on the global module table yet (deps must be ready first)",
                    row.alias,
                    row.path.display()
                ));
            }
        }
        Ok(())
    }

    /// Mount a module folder onto the global table (config only; no `.lit` run).
    ///
    /// Same path → silent merge. Caller's readiness: before using this module's
    /// own imports, call `ensure_imports_ready` on its `litex_config`.
    pub fn mount_module(
        &mut self,
        name: String,
        path: PathBuf,
        litex_config: LitexConfig,
    ) -> Result<usize, String> {
        self.record_import(name, path, litex_config)
    }
}
