mod module_records;
mod project_config;
mod registry;
mod repository_discovery;

pub use module_records::{
    BareSymbolSourceKind, ConfigBareSymbolSource, ConfigImport, ConfigImportKind, ExportEntry,
    FileId, FileRunner, FileStatus, ImportTarget, ModuleId, ModuleRunner, ModuleStatus,
};
pub use project_config::{
    parse_project_config, ProjectBareName, ProjectConfig, ProjectExport, ProjectHierarchy,
    ProjectImport, ProjectStdImport,
};
pub use registry::{ModuleManager, UnverifiedImport};
pub use repository_discovery::{
    discover_repository, discover_repository_for_file, resolve_std_root, RepositoryFileTarget,
};
pub(super) use repository_discovery::{
    discover_terminal_module_import, discover_terminal_std_import,
};
