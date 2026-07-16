mod module_manager;
mod module_runner;
mod project_config;
mod repository;

pub use module_manager::{ModuleManager, KERNEL_PATH};
pub use module_runner::{
    ConfigImport, ExportEntry, FileId, FileRunner, FileStatus, ImportTarget, ModuleId,
    ModuleRunner, ModuleStatus,
};
pub use project_config::{
    parse_project_config, ProjectConfig, ProjectExport, ProjectImport, ProjectRequirement,
    ProjectStdImport,
};
pub use repository::{
    discover_repository, discover_repository_for_file, discover_std_module, resolve_std_root,
    RepositoryFileTarget,
};
