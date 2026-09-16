//! Elaborate surface `::` / `:::` name parts into id-based `AtomicName`.

use crate::new_pipeline::ast::names::AtomicName;

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

    /// `a:::b` flatten sugar: import alias `a` with exactly one export → that file + `b`.
    pub fn elaborate_flat_import(&self, alias: &str, name: String) -> Result<AtomicName, String> {
        let mod_id = self.mod_id_for_local_alias(alias)?;
        let module = self
            .imports
            .get(mod_id)
            .ok_or_else(|| format!("unknown mod_id {mod_id}"))?;
        if module.litex_config.exports.len() != 1 {
            return Err(format!(
                "`{alias}:::…` requires imported module `{}` to have exactly one [export], found {}",
                module.name,
                module.litex_config.exports.len()
            ));
        }
        Ok(AtomicName::WithModAndExportFileId {
            mod_id,
            file_id: 0,
            name,
        })
    }

    /// Turn surface segments into `AtomicName`.
    ///
    /// - 1 segment: `Plain`
    /// - 2 segments: current-module export `a` + name `b` → `WithMod`
    /// - 3 segments: import alias `a` + export `b` + name `c` → `WithModAndExport`
    ///
    /// `a:::b` is handled by `elaborate_flat_import`, not this function.
    pub fn elaborate_name_parts(&self, parts: &[String]) -> Result<AtomicName, String> {
        match parts.len() {
            1 => Ok(AtomicName::Plain {
                name: parts[0].clone(),
            }),
            2 => {
                let file_id = self.file_id_in_current(&parts[0])?;
                Ok(AtomicName::WithExportFileId {
                    file_id,
                    name: parts[1].clone(),
                })
            }
            3 => {
                let mod_id = self.mod_id_for_local_alias(&parts[0])?;
                let file_id = self.file_id_in_mod(mod_id, &parts[1])?;
                Ok(AtomicName::WithModAndExportFileId {
                    mod_id,
                    file_id,
                    name: parts[2].clone(),
                })
            }
            _ => Err("qualified name must be `a::b`, `a:::b`, or `a::b::c`".to_string()),
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
        let path = config
            .imports
            .iter()
            .find(|row| row.alias == alias)
            .map(|row| row.path.clone())
            .ok_or_else(|| format!("unknown import alias `{alias}` in the current module"))?;
        self.path_to_mod_id.get(&path).copied().ok_or_else(|| {
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
