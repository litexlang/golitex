//! new_pipeline module world: global mounts, litex.config shapes, export envs.
//!
//! Design contract: [`README.md`](README.md).

mod elaborate_name;
mod export_file;
mod global_module_manager;
mod imported_module;
mod litex_config;
mod mount;
mod parse_litex_config;

pub use export_file::ExportFileAndItsExecEnv;
pub use global_module_manager::GlobalModuleManager;
pub use imported_module::ImportedModule;
pub use litex_config::{LitexConfig, LitexConfigExport, LitexConfigImport};
pub use parse_litex_config::parse_litex_config;
