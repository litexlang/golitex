//! Orchestrate config → mount → run `.lit` → record env (`-r`).
//!
//! Design contract: [`README.md`](README.md).

mod import_kb;
mod load_config;
mod mount_cwd_config;
mod run_export_file;
mod run_file_with_config;
mod run_import_module;
mod run_project;

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "../../tests/unit/run_module/error_forwarding/tests.rs"]
mod error_forwarding_tests;

#[cfg(test)]
#[path = "../../tests/unit/run_module/strict_cache/tests.rs"]
mod strict_cache_tests;

#[cfg(test)]
#[path = "../../tests/unit/run_module/qualified_struct_views.rs"]
mod qualified_struct_view_tests;

pub use load_config::{
    litex_config_path, load_config, load_config_or_empty, normalize_module_dir, resolve_std_root,
    LITEX_CONFIG_FILE_NAME,
};
pub use mount_cwd_config::{mount_cwd_config, MountCwdConfigOutcome};
pub use run_export_file::run_export_file;
pub use run_file_with_config::run_file_with_config;
pub use run_import_module::{run_import_module, RunImportModuleOutcome};
pub use run_project::run_project;

pub(crate) use mount_cwd_config::mount_cwd_config_with_graph;
pub(crate) use run_file_with_config::run_file_with_config_with_graph;
pub(crate) use run_project::run_project_with_graph;
