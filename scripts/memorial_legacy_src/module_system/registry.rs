use crate::prelude::*;
use std::collections::HashMap;

/// Owns every module participating in one top-level Runtime.
///
/// Module runners refer to dependencies by `ModuleId`; they never hold Runtime
/// or runner references. This keeps all cross-module lookup and lifecycle state
/// inside one per-run registry.
#[derive(Clone)]
pub struct ModuleManager {
    /// All modules participating in this top-level run, keyed by stable ID.
    pub modules: HashMap<ModuleId, ModuleRunner>,

    /// Maps canonical module names to their stable IDs.
    pub module_by_name: HashMap<String, ModuleId>,

    /// Maps canonical real module-root paths to module IDs.
    pub module_by_root: HashMap<RealDirectoryPath, ModuleId>,

    /// Maps canonical exported-file names to their import targets.
    ///
    /// Name resolution uses this index to locate the source environment for
    /// namespaces such as `A::one` and `gf::main`.
    pub exported_files_by_name: HashMap<String, ImportTarget>,

    /// Module IDs currently being loaded, in discovery order.
    ///
    /// The stack is used to detect cyclic imports and unwind loading state.
    pub loading_module_stack: Vec<ModuleId>,

    /// Next module ID to allocate.
    pub next_module_id: usize,

    /// Records dependencies loaded without verification in ordinary mode.
    ///
    /// Run summaries report these imports, and definition graphs preserve
    /// their trust provenance. This list is usually empty in `-strict` mode
    /// because dependencies are verified.
    pub unverified_imports: Vec<UnverifiedImport>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnverifiedImportKind {
    /// A project module loaded from a configuration import.
    ProjectImport,
    /// A project export target loaded without verification.
    ProjectExport,
    /// A module loaded by a terminal `import` command.
    TerminalImport,
    /// A standard-library module loaded by a terminal `import std` command.
    TerminalStdImport,
}

impl UnverifiedImportKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ProjectImport => "project_import",
            Self::ProjectExport => "project_export",
            Self::TerminalImport => "terminal_import",
            Self::TerminalStdImport => "terminal_std_import",
        }
    }
}

#[derive(Clone, Debug)]
pub struct UnverifiedImport {
    /// Kind of dependency load, represented by the closed set of load paths.
    pub kind: UnverifiedImportKind,

    /// Canonical name of the dependency loaded without verification.
    pub name: String,

    /// Source location that caused the dependency to be loaded.
    pub line_file: LineFile,
}

impl ModuleManager {
    pub fn new() -> Self {
        ModuleManager {
            modules: HashMap::new(),
            module_by_name: HashMap::new(),
            module_by_root: HashMap::new(),
            exported_files_by_name: HashMap::new(),
            loading_module_stack: vec![],
            next_module_id: 0,
            unverified_imports: vec![],
        }
    }

    #[deprecated(note = "use create_virtual_root_module or create_file_root_module")]
    pub fn create_root_module(
        &mut self,
        main_file_path: &str,
        legacy_virtual_source: bool,
    ) -> SourceId {
        if legacy_virtual_source {
            let kind = match main_file_path.to_ascii_lowercase().as_str() {
                "eval" => VirtualSource::Eval,
                "repl" => VirtualSource::Repl,
                "session" => VirtualSource::Session,
                "to-lean" | "to_lean" => VirtualSource::ToLean,
                "to-latex" | "to_latex" => VirtualSource::ToLatex,
                _ => VirtualSource::Named(main_file_path.to_string()),
            };
            self.create_virtual_root_module(kind)
        } else {
            self.create_file_root_module(RealFilePath::new(main_file_path))
        }
    }

    pub fn create_virtual_root_module(&mut self, kind: VirtualSource) -> SourceId {
        self.create_root_source(SourcePath::VirtualSource(kind))
    }

    pub fn create_file_root_module(&mut self, path: RealFilePath) -> SourceId {
        self.create_root_source(SourcePath::RealFilePath(path))
    }

    fn create_root_source(&mut self, origin: SourcePath) -> SourceId {
        assert!(
            self.module(ModuleId::ROOT).is_none(),
            "root module has already been created"
        );
        let id = self.allocate_module_id();
        assert_eq!(
            id,
            ModuleId::ROOT,
            "the root module must be allocated as ModuleId::ROOT"
        );
        let mut runner = ModuleRunner::new(
            id,
            String::new(),
            ModuleLocation::Virtual,
            ProjectHierarchy::Module,
            None,
            ModuleStatus::Loaded,
        );
        let source_id = match origin {
            SourcePath::VirtualSource(kind) => runner.create_virtual_source(kind),
            SourcePath::RealFilePath(path) => runner.create_real_source(path.0, None),
        };
        runner.module_source_id = Some(source_id);
        if matches!(
            runner.source(source_id).map(|source| &source.origin),
            Some(SourcePath::RealFilePath(_))
        ) {
            runner.location = ModuleLocation::SingleFile;
        }
        runner
            .source_mut(source_id)
            .expect("root source file should exist")
            .load_status = SourceLoadStatus::Loaded;
        self.modules.insert(id, runner);
        source_id
    }

    pub fn create_repository_root_module(
        &mut self,
        module_root_path: RealDirectoryPath,
        main_file_path: RealFilePath,
    ) -> Result<ModuleId, String> {
        if self.module(ModuleId::ROOT).is_some() {
            return Err("root module has already been created".to_string());
        }
        let id = self.allocate_module_id();
        if id != ModuleId::ROOT {
            return Err("the root module must be allocated as ModuleId::ROOT".to_string());
        }
        let runner = ModuleRunner::new(
            id,
            String::new(),
            ModuleLocation::Repository {
                root: module_root_path.clone(),
                manifest: main_file_path.clone(),
            },
            ProjectHierarchy::Module,
            None,
            ModuleStatus::Loaded,
        );
        self.modules.insert(id, runner);
        self.module_by_root.insert(module_root_path, id);
        Ok(id)
    }

    /// Convert a constructor-created virtual root into a repository root.
    /// The already-registered root source stays active so Runtime never loses
    /// its `(ModuleId, SourceId)` pair while discovery builds the export tree.
    pub fn configure_repository_root_module(
        &mut self,
        module_root_path: RealDirectoryPath,
        main_file_path: RealFilePath,
    ) -> Result<ModuleId, String> {
        let Some(module) = self.module_mut(ModuleId::ROOT) else {
            return Err("runtime root module is missing".to_string());
        };
        if module.location != ModuleLocation::Virtual
            || module.module_source_id != Some(SourceId(0))
            || module.sources.len() != 1
        {
            return Err("root module has already been configured".to_string());
        }
        module.location = ModuleLocation::Repository {
            root: module_root_path.clone(),
            manifest: main_file_path,
        };
        self.module_by_root.insert(module_root_path, ModuleId::ROOT);
        Ok(ModuleId::ROOT)
    }

    pub fn create_discovered_module(
        &mut self,
        module_name: String,
        module_root_path: RealDirectoryPath,
        main_file_path: RealFilePath,
        hierarchy: ProjectHierarchy,
        parent_module_id: Option<ModuleId>,
    ) -> Result<ModuleId, String> {
        if self.module_by_name.contains_key(&module_name) {
            return Err(format!(
                "module name `{}` has already been used",
                module_name
            ));
        }
        let id = self.allocate_module_id();
        let mut runner = ModuleRunner::new(
            id,
            module_name.clone(),
            ModuleLocation::Repository {
                root: module_root_path.clone(),
                manifest: main_file_path.clone(),
            },
            hierarchy,
            parent_module_id,
            ModuleStatus::Discovered,
        );
        if main_file_path
            .as_path()
            .extension()
            .is_some_and(|ext| ext == "lit")
        {
            runner.create_module_source(main_file_path.to_string(), module_name.clone());
        }
        self.modules.insert(id, runner);
        self.module_by_name.insert(module_name, id);
        self.module_by_root.entry(module_root_path).or_insert(id);
        Ok(id)
    }

    pub fn create_discovered_standard_module(
        &mut self,
        module_name: String,
        module_root_path: RealDirectoryPath,
        main_file_path: RealFilePath,
        hierarchy: ProjectHierarchy,
        parent_module_id: Option<ModuleId>,
    ) -> Result<ModuleId, String> {
        let module_id = self.create_discovered_module(
            module_name,
            module_root_path,
            main_file_path,
            hierarchy,
            parent_module_id,
        )?;
        self.module_mut(module_id)
            .expect("new standard-library module should exist")
            .is_standard_library = true;
        Ok(module_id)
    }

    pub fn register_exported_file(
        &mut self,
        canonical_name: String,
        target: ImportTarget,
    ) -> Result<(), String> {
        if self
            .exported_files_by_name
            .insert(canonical_name.clone(), target)
            .is_some()
        {
            return Err(format!(
                "duplicate canonical exported file name `{}`",
                canonical_name
            ));
        }
        Ok(())
    }

    pub fn import_target_by_canonical_name(&self, name: &str) -> Option<ImportTarget> {
        if let Some(module_id) = self.module_id_by_name(name) {
            return Some(ImportTarget::Module(module_id));
        }
        self.exported_files_by_name.get(name).copied()
    }

    pub fn canonical_name_for_target(&self, target: ImportTarget) -> Option<&str> {
        match target {
            ImportTarget::Module(module_id) => self
                .module(module_id)
                .map(|module| module.module_name.as_str()),
            ImportTarget::File {
                module_id,
                source_id,
            } => self
                .module(module_id)?
                .source(source_id)?
                .canonical_name
                .as_deref(),
        }
    }

    pub fn canonical_name_for_reference(
        &self,
        owner_module_id: ModuleId,
        name: &str,
    ) -> Option<String> {
        let mut current_module_id = Some(owner_module_id);
        while let Some(module_id) = current_module_id {
            let module = self.module(module_id)?;
            for config_import in module.config_imports.iter() {
                if let Some(suffix) = local_reference_suffix(name, config_import.name.as_str()) {
                    let canonical_root = self
                        .canonical_name_for_target(ImportTarget::Module(config_import.module_id))?;
                    let candidate = format!("{}{}", canonical_root, suffix);
                    if self
                        .import_target_by_canonical_name(candidate.as_str())
                        .is_some()
                    {
                        return Some(candidate);
                    }
                }
            }
            for (export_name, export_entry) in module.exports.iter() {
                if let Some(suffix) = local_reference_suffix(name, export_name.as_str()) {
                    let canonical_root =
                        self.canonical_name_for_target(export_entry.target(module_id))?;
                    let candidate = format!("{}{}", canonical_root, suffix);
                    if self
                        .import_target_by_canonical_name(candidate.as_str())
                        .is_some()
                    {
                        return Some(candidate);
                    }
                }
            }
            current_module_id = module.parent_module_id;
        }
        self.import_target_by_canonical_name(name)
            .map(|_| name.to_string())
    }

    pub fn module(&self, id: ModuleId) -> Option<&ModuleRunner> {
        self.modules.get(&id)
    }

    pub fn module_mut(&mut self, id: ModuleId) -> Option<&mut ModuleRunner> {
        self.modules.get_mut(&id)
    }

    #[deprecated(note = "use create_virtual_source")]
    pub fn create_execution_file(
        &mut self,
        module_id: ModuleId,
        legacy_label: &str,
    ) -> Result<SourceId, String> {
        let kind = match legacy_label.to_ascii_lowercase().as_str() {
            "eval" => VirtualSource::Eval,
            "repl" => VirtualSource::Repl,
            "session" => VirtualSource::Session,
            "to-lean" | "to_lean" => VirtualSource::ToLean,
            "to-latex" | "to_latex" => VirtualSource::ToLatex,
            _ => VirtualSource::Named(legacy_label.to_string()),
        };
        let source_id = self.create_virtual_source(module_id, kind)?;
        Ok(source_id)
    }

    pub fn create_virtual_source(
        &mut self,
        module_id: ModuleId,
        kind: VirtualSource,
    ) -> Result<SourceId, String> {
        let source_id = self
            .module_mut(module_id)
            .ok_or_else(|| "execution module is missing".to_string())?
            .create_virtual_source(kind);
        self.module_mut(module_id)
            .and_then(|module| module.source_mut(source_id))
            .expect("new virtual source should exist")
            .load_status = SourceLoadStatus::Loaded;
        Ok(source_id)
    }

    pub fn module_is_descendant_of(
        &self,
        module_id: ModuleId,
        ancestor_module_id: ModuleId,
    ) -> bool {
        let mut current_module_id = Some(module_id);
        while let Some(current) = current_module_id {
            if current == ancestor_module_id {
                return true;
            }
            current_module_id = self
                .module(current)
                .and_then(|module| module.parent_module_id);
        }
        false
    }

    pub fn module_id_by_name(&self, module_name: &str) -> Option<ModuleId> {
        self.module_by_name.get(module_name).copied()
    }

    pub fn module_id_by_root_path(&self, module_root_path: &RealDirectoryPath) -> Option<ModuleId> {
        self.module_by_root.get(module_root_path).copied()
    }

    /// Compatibility adapter for callers that still receive a root path as a
    /// string at an external boundary.
    pub fn module_id_by_path(&self, module_root_path: &str) -> Option<ModuleId> {
        self.module_id_by_root_path(&RealDirectoryPath::new(module_root_path))
    }

    pub fn finish_loading_module(&mut self, module_id: ModuleId) {
        if let Some(module) = self.modules.get_mut(&module_id) {
            module.status = ModuleStatus::Loaded;
        }
        if self.loading_module_stack.last() == Some(&module_id) {
            self.loading_module_stack.pop();
        } else if let Some(index) = self
            .loading_module_stack
            .iter()
            .rposition(|loading_id| *loading_id == module_id)
        {
            self.loading_module_stack.remove(index);
        }
    }

    pub fn begin_loading_discovered_module(&mut self, module_id: ModuleId) -> Result<(), String> {
        let Some(module) = self.modules.get(&module_id) else {
            return Err("discovered module is missing".to_string());
        };
        if module.status == ModuleStatus::Loading {
            let cycle_start_index = self
                .loading_module_stack
                .iter()
                .position(|loading_id| *loading_id == module_id)
                .unwrap_or(0);
            let mut cycle_names = self.loading_module_stack[cycle_start_index..]
                .iter()
                .filter_map(|loading_id| self.modules.get(loading_id))
                .map(|loading_module| loading_module.module_name.clone())
                .collect::<Vec<String>>();
            cycle_names.push(module.module_name.clone());
            return Err(format!(
                "cyclic module import: {}",
                cycle_names.join(" -> ")
            ));
        }
        if module.status == ModuleStatus::Loaded {
            return Ok(());
        }

        self.modules
            .get_mut(&module_id)
            .expect("discovered module should exist")
            .status = ModuleStatus::Loading;
        self.loading_module_stack.push(module_id);
        Ok(())
    }

    fn allocate_module_id(&mut self) -> ModuleId {
        let id = ModuleId(self.next_module_id);
        self.next_module_id += 1;
        id
    }
}

fn local_reference_suffix(name: &str, local_root: &str) -> Option<String> {
    if name == local_root {
        return Some(String::new());
    }
    name.strip_prefix(local_root)
        .filter(|suffix| suffix.starts_with(MOD_SIGN))
        .map(str::to_string)
}

#[cfg(test)]
mod tests {
    use super::UnverifiedImportKind;

    #[test]
    fn unverified_import_kinds_keep_stable_labels() {
        assert_eq!(
            UnverifiedImportKind::ProjectImport.as_str(),
            "project_import"
        );
        assert_eq!(
            UnverifiedImportKind::ProjectExport.as_str(),
            "project_export"
        );
        assert_eq!(
            UnverifiedImportKind::TerminalImport.as_str(),
            "terminal_import"
        );
        assert_eq!(
            UnverifiedImportKind::TerminalStdImport.as_str(),
            "terminal_std_import"
        );
    }
}
