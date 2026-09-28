mod module_records;
mod project_config;
mod registry;
mod repository_discovery;

pub use module_records::{
    ConfigImport, ConfigImportKind, ExportEntry, ImportTarget, ModuleId, ModuleLocation,
    ModuleRunner, ModuleStatus, RealDirectoryPath, RealFilePath, Source, SourceId,
    SourceLoadStatus, SourcePath, VirtualSource,
};
pub use project_config::{
    parse_project_config, ProjectConfig, ProjectExport, ProjectHierarchy, ProjectImport,
    ProjectStdImport,
};
pub use registry::{ModuleManager, UnverifiedImport, UnverifiedImportKind};
pub use repository_discovery::{
    discover_repository, discover_repository_for_file, resolve_std_root, RepositoryFileTarget,
};
pub(super) use repository_discovery::{
    discover_terminal_module_import, discover_terminal_std_import,
};
