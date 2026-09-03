use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(pub usize);

impl ModuleId {
    pub const ROOT: Self = Self(0);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceId(pub usize);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RealFilePath(pub PathBuf);

impl RealFilePath {
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self(path.into())
    }

    pub fn as_path(&self) -> &Path {
        self.0.as_path()
    }
}

impl AsRef<Path> for RealFilePath {
    fn as_ref(&self) -> &Path {
        self.as_path()
    }
}

impl fmt::Display for RealFilePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.display().fmt(f)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RealDirectoryPath(pub PathBuf);

impl RealDirectoryPath {
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self(path.into())
    }

    pub fn as_path(&self) -> &Path {
        self.0.as_path()
    }
}

impl AsRef<Path> for RealDirectoryPath {
    fn as_ref(&self) -> &Path {
        self.as_path()
    }
}

impl fmt::Display for RealDirectoryPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.display().fmt(f)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VirtualSource {
    Eval,
    Repl,
    Session,
    ToLean,
    ToLatex,
    CodeExtraction,
    /// A virtual source whose name is meaningful but not a fixed runtime
    /// category (for example an embedding-specific projection).
    Named(String),
}

impl VirtualSource {
    pub fn label(&self) -> &str {
        match self {
            VirtualSource::Eval => "eval",
            VirtualSource::Repl => "repl",
            VirtualSource::Session => "session",
            VirtualSource::ToLean => "to-lean",
            VirtualSource::ToLatex => "to-latex",
            VirtualSource::CodeExtraction => "code-extraction",
            VirtualSource::Named(name) => name.as_str(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SourcePath {
    RealFilePath(RealFilePath),
    VirtualSource(VirtualSource),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModuleLocation {
    /// A discovered repository module; the manifest is configuration, not a Source.
    Repository {
        root: RealDirectoryPath,
        manifest: RealFilePath,
    },
    /// A standalone real file module with its source held in `ModuleRunner::sources`.
    SingleFile,
    /// A standalone virtual module such as eval or REPL.
    Virtual,
}

impl ModuleLocation {
    pub fn root_path(&self) -> Option<&RealDirectoryPath> {
        match self {
            ModuleLocation::Repository { root, .. } => Some(root),
            ModuleLocation::SingleFile | ModuleLocation::Virtual => None,
        }
    }

    pub fn manifest_path(&self) -> Option<&RealFilePath> {
        match self {
            ModuleLocation::Repository { manifest, .. } => Some(manifest),
            ModuleLocation::SingleFile | ModuleLocation::Virtual => None,
        }
    }

    pub fn display_label(&self) -> String {
        match self {
            ModuleLocation::Repository { manifest, .. } => manifest.to_string(),
            ModuleLocation::SingleFile => "single-file-module".to_string(),
            ModuleLocation::Virtual => "virtual-module".to_string(),
        }
    }
}

impl SourcePath {
    pub fn display_label(&self) -> String {
        match self {
            SourcePath::RealFilePath(path) => path.to_string(),
            SourcePath::VirtualSource(kind) => kind.label().to_string(),
        }
    }

    pub fn real_file_path(&self) -> Option<&RealFilePath> {
        match self {
            SourcePath::RealFilePath(path) => Some(path),
            SourcePath::VirtualSource(_) => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceLoadStatus {
    Unloaded,
    Loading,
    Loaded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleStatus {
    Discovered,
    Loading,
    Loaded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ImportTarget {
    File {
        module_id: ModuleId,
        source_id: SourceId,
    },
    Module(ModuleId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportEntry {
    File { name: String, source_id: SourceId },
    Module { name: String, module_id: ModuleId },
}

#[derive(Clone)]
pub struct ConfigImport {
    pub name: String,
    pub module_id: ModuleId,
    pub kind: ConfigImportKind,
    pub line_file: LineFile,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConfigImportKind {
    Path,
    Standard,
}

impl ExportEntry {
    pub fn target(&self, owner_module: ModuleId) -> ImportTarget {
        match self {
            ExportEntry::File { source_id, .. } => ImportTarget::File {
                module_id: owner_module,
                source_id: *source_id,
            },
            ExportEntry::Module { module_id, .. } => ImportTarget::Module(*module_id),
        }
    }
}

#[derive(Clone)]
pub struct Source {
    /// Stable identifier within the owning module.
    pub id: SourceId,
    /// Semantic origin.  A virtual source never participates in filesystem
    /// discovery or real-file authorization.
    pub origin: SourcePath,
    /// Namespace name used by imports/exports; virtual sources do not need one.
    pub canonical_name: Option<String>,
    /// Persistent checked environment owned by this source.
    pub environment: Box<Environment>,
    /// Lifecycle state for repository loading; virtual sources are ready when created.
    pub load_status: SourceLoadStatus,
    /// Verification policy used when this source was loaded.  This is source
    /// provenance for graph/output projection, not the runtime's active mode.
    pub load_mode: ExecutionMode,
}

impl Source {
    pub fn new(id: SourceId, origin: SourcePath, canonical_name: Option<String>) -> Self {
        Source {
            id,
            origin,
            canonical_name,
            environment: Box::new(Environment::new_empty_env()),
            load_status: SourceLoadStatus::Unloaded,
            load_mode: ExecutionMode::RequireVerification,
        }
    }

    pub fn display_label(&self) -> String {
        self.origin.display_label()
    }

    pub fn real_file_path(&self) -> Option<&RealFilePath> {
        self.origin.real_file_path()
    }
}

#[derive(Clone)]
pub struct ModuleRunner {
    /// Stable module identity in the run's module registry.
    pub id: ModuleId,
    /// Canonical namespace used by imports; empty for the root module.
    pub module_name: String,
    /// Repository/file ownership metadata, kept separate from SourcePath.
    pub location: ModuleLocation,
    pub hierarchy: ProjectHierarchy,
    pub parent_module_id: Option<ModuleId>,
    pub is_standard_library: bool,
    /// Module-level state for repository configuration; source environments live in `sources`.
    pub main_environment: Box<Environment>,
    pub sources: Vec<Source>,
    /// The source owned directly by a module, whether physical or virtual.
    pub module_source_id: Option<SourceId>,
    /// Optional projection source representing a module's flattened exports.
    pub flattened_export_source: Option<SourceId>,
    pub exports: HashMap<String, ExportEntry>,
    pub run_targets: Vec<ImportTarget>,
    pub run_target_lines: HashMap<ImportTarget, LineFile>,
    pub config_imports: Vec<ConfigImport>,
    pub status: ModuleStatus,
    /// Verification policy used while loading the module-owned environment.
    pub load_mode: ExecutionMode,
}

impl ModuleRunner {
    pub fn new(
        id: ModuleId,
        module_name: String,
        location: ModuleLocation,
        hierarchy: ProjectHierarchy,
        parent_module_id: Option<ModuleId>,
        status: ModuleStatus,
    ) -> Self {
        ModuleRunner {
            id,
            module_name,
            location,
            hierarchy,
            parent_module_id,
            is_standard_library: false,
            main_environment: Box::new(Environment::new_empty_env()),
            sources: vec![],
            module_source_id: None,
            flattened_export_source: None,
            exports: HashMap::new(),
            run_targets: vec![],
            run_target_lines: HashMap::new(),
            config_imports: vec![],
            status,
            load_mode: ExecutionMode::RequireVerification,
        }
    }

    pub fn create_exported_source(
        &mut self,
        source_path: String,
        canonical_name: String,
    ) -> SourceId {
        self.create_real_source(source_path, Some(canonical_name))
    }

    pub fn create_real_source(
        &mut self,
        source_path: impl Into<PathBuf>,
        canonical_name: Option<String>,
    ) -> SourceId {
        let id = SourceId(self.sources.len());
        self.sources.push(Source::new(
            id,
            SourcePath::RealFilePath(RealFilePath::new(source_path)),
            canonical_name,
        ));
        id
    }

    pub fn create_virtual_source(&mut self, kind: VirtualSource) -> SourceId {
        let id = SourceId(self.sources.len());
        self.sources
            .push(Source::new(id, SourcePath::VirtualSource(kind), None));
        id
    }

    pub fn create_module_source(
        &mut self,
        source_path: String,
        canonical_name: String,
    ) -> SourceId {
        assert!(
            self.module_source_id.is_none(),
            "module source file has already been registered"
        );
        let source_id = self.create_real_source(source_path, Some(canonical_name));
        self.module_source_id = Some(source_id);
        source_id
    }

    pub fn source_id_by_real_file_path(&self, source_path: &RealFilePath) -> Option<SourceId> {
        self.sources
            .iter()
            .find(|source| {
                source
                    .real_file_path()
                    .is_some_and(|path| path == source_path)
            })
            .map(|source| source.id)
    }

    /// Compatibility adapter for path strings received at external boundaries.
    pub fn source_id_by_real_path(&self, source_path: &str) -> Option<SourceId> {
        self.source_id_by_real_file_path(&RealFilePath::new(source_path))
    }

    pub fn source(&self, id: SourceId) -> Option<&Source> {
        self.sources.get(id.0)
    }

    pub fn source_mut(&mut self, id: SourceId) -> Option<&mut Source> {
        self.sources.get_mut(id.0)
    }

    pub fn root_directory_path(&self) -> Option<&RealDirectoryPath> {
        self.location.root_path()
    }

    pub fn manifest_file_path(&self) -> Option<&RealFilePath> {
        self.location.manifest_path()
    }

    pub fn main_source_label(&self) -> String {
        self.module_source_id
            .and_then(|id| self.source(id))
            .map(Source::display_label)
            .unwrap_or_else(|| self.location.display_label())
    }
}

#[cfg(test)]
#[path = "../../tests/unit/module_system/source_records/tests.rs"]
mod source_records_tests;
