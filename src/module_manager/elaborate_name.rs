//! Elaborate `::` paths and config aliases into id-based `AtomicName`.

use crate::ast::names::AtomicName;

use super::global_module_manager::GlobalModuleManager;
use super::litex_config::LitexConfig;

impl GlobalModuleManager {
    /// Config of the module that owns the file currently being parsed/run.
    /// Uses `self.current_mod_id`: `None` → root config.
    pub fn current_litex_config(&self) -> Result<&LitexConfig, String> {
        match self.current_mod_id {
            None => Ok(&self.litex_config),
            Some(mod_id) => self
                .imports
                .get(mod_id)
                .map(|m| &m.litex_config)
                .ok_or_else(|| format!("unknown current mod_id {mod_id}")),
        }
    }

    /// Retained entry point solely for the removed-syntax diagnostic.
    pub fn elaborate_flat_import(&self, alias: &str, name: String) -> Result<AtomicName, String> {
        Err(format!(
            "`:::` has been removed: replace `{alias}:::{name}` with `{alias}::export::{name}`, or configure `[alias] short = {alias}::export` and use `short::{name}` (replace `export` with the actual export name)"
        ))
    }

    /// Check every target after imports are mounted, including unused aliases and cache hits.
    pub fn validate_alias_targets(&self, config: &LitexConfig) -> Result<(), String> {
        for alias in &config.aliases {
            let mod_id = self.mod_id_for_alias_in_config(config, &alias.import_alias)?;
            self.file_id_in_mod(mod_id, &alias.export_name)
                .map_err(|message| {
                    format!(
                        "namespace alias `{}` = {}::{}: {message}",
                        alias.name, alias.import_alias, alias.export_name
                    )
                })?;
        }
        Ok(())
    }

    /// Turn surface segments into `AtomicName`.
    ///
    /// - 1 segment: `Plain`
    /// - 2 segments: configured namespace alias, otherwise current-module export
    /// - 3 segments: import alias `a` + export `b` + name `c` → `WithModAndExportFileId`
    ///
    /// Alias expansion never changes the declaration's module/file identity.
    pub fn elaborate_name_parts(&self, parts: &[String]) -> Result<AtomicName, String> {
        match parts.len() {
            1 => Ok(AtomicName::Plain {
                name: parts[0].clone(),
            }),
            2 => {
                if let Some(alias) = self
                    .current_litex_config()?
                    .aliases
                    .iter()
                    .find(|alias| alias.name == parts[0])
                {
                    let global_mod_id = self.mod_id_for_local_alias(&alias.import_alias)?;
                    let export_file_id = self.file_id_in_mod(global_mod_id, &alias.export_name)?;
                    return Ok(AtomicName::WithModAndExportFileId {
                        global_mod_id,
                        export_file_id,
                        name: parts[1].clone(),
                    });
                }
                let export_file_id = self.file_id_in_current(&parts[0])?;
                match self.current_mod_id {
                    Some(global_mod_id) => Ok(AtomicName::WithModAndExportFileId {
                        global_mod_id,
                        export_file_id,
                        name: parts[1].clone(),
                    }),
                    None => Ok(AtomicName::WithExportFileId {
                        export_file_id,
                        name: parts[1].clone(),
                    }),
                }
            }
            3 => {
                let global_mod_id = self.mod_id_for_local_alias(&parts[0])?;
                let export_file_id = self.file_id_in_mod(global_mod_id, &parts[1])?;
                Ok(AtomicName::WithModAndExportFileId {
                    global_mod_id,
                    export_file_id,
                    name: parts[2].clone(),
                })
            }
            _ => Err("qualified name must be `a::b` or `a::b::c`".to_string()),
        }
    }

    fn file_id_in_current(&self, export_name: &str) -> Result<usize, String> {
        let config = self.current_litex_config()?;
        index_of_export(config, export_name).ok_or_else(|| {
            format!("unknown export `{export_name}` in the current module's litex.config")
        })
    }

    fn file_id_in_mod(&self, mod_id: usize, export_name: &str) -> Result<usize, String> {
        let module = self
            .imports
            .get(mod_id)
            .ok_or_else(|| format!("unknown mod_id {mod_id}"))?;
        index_of_export(&module.litex_config, export_name).ok_or_else(|| {
            format!(
                "unknown export `{export_name}` in imported module `{}`",
                module.name
            )
        })
    }

    fn mod_id_for_local_alias(&self, alias: &str) -> Result<usize, String> {
        let config = self.current_litex_config()?;
        self.mod_id_for_alias_in_config(config, alias)
    }

    fn mod_id_for_alias_in_config(
        &self,
        config: &LitexConfig,
        alias: &str,
    ) -> Result<usize, String> {
        let path = config
            .imports
            .iter()
            .find(|row| row.alias == alias)
            .map(|row| row.path.clone())
            .ok_or_else(|| format!("unknown import alias `{alias}` in the current module"))?;
        // Mount keys use canonicalize (see run_module::normalize_module_dir);
        // config rows keep normalize_join spelling. Align before lookup.
        let key = path.canonicalize().unwrap_or_else(|_| path.clone());
        self.path_to_mod_id.get(&key).copied().ok_or_else(|| {
            format!(
                "import alias `{alias}` path is not on the global module table yet (deps must be ready first)"
            )
        })
    }
}

fn index_of_export(config: &LitexConfig, export_name: &str) -> Option<usize> {
    config
        .exports
        .iter()
        .position(|row| row.name == export_name)
}
