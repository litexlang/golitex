//! Orchestrate config → mount → run `.lit` → record env (`-r`).
//!
//! Design contract: [`README.md`](README.md).

mod load_config;
mod run_export_file;
mod run_file_with_config;
mod run_import_module;
mod run_project;

#[cfg(test)]
mod tests;

pub use load_config::{
    litex_config_path, load_config, load_config_or_empty, normalize_module_dir, resolve_std_root,
    LITEX_CONFIG_FILE_NAME,
};
pub use run_export_file::run_export_file;
pub use run_file_with_config::run_file_with_config;
pub use run_import_module::{run_import_module, RunImportModuleOutcome};
pub use run_project::run_project;
