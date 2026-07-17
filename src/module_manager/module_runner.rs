use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileStatus {
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
        file_id: FileId,
    },
    Module(ModuleId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportEntry {
    File { name: String, file_id: FileId },
    Module { name: String, module_id: ModuleId },
}

#[derive(Clone)]
pub struct ConfigImport {
    pub name: String,
    pub module_id: ModuleId,
    pub line_file: LineFile,
}

impl ExportEntry {
    pub fn target(&self, owner_module: ModuleId) -> ImportTarget {
        match self {
            ExportEntry::File { file_id, .. } => ImportTarget::File {
                module_id: owner_module,
                file_id: *file_id,
            },
            ExportEntry::Module { module_id, .. } => ImportTarget::Module(*module_id),
        }
    }
}

#[derive(Clone)]
pub struct FileRunner {
    pub id: FileId,
    pub source_path: String,
    pub canonical_name: String,
    pub environment: Box<Environment>,
    pub imported_modules: Vec<ModuleId>,
    pub status: FileStatus,
    pub execution_mode: ExecutionMode,
    pub strictly_verified: bool,
}

impl FileRunner {
    pub fn new(id: FileId, source_path: String, canonical_name: String) -> Self {
        FileRunner {
            id,
            source_path,
            canonical_name,
            environment: Box::new(Environment::new_empty_env()),
            imported_modules: vec![],
            status: FileStatus::Unloaded,
            execution_mode: ExecutionMode::Verified,
            strictly_verified: false,
        }
    }
}

#[derive(Clone)]
pub struct ModuleRunner {
    pub id: ModuleId,
    pub module_name: String,
    pub module_root_path: String,
    pub main_file_path: String,
    pub hierarchy: ProjectHierarchy,
    pub parent_module_id: Option<ModuleId>,
    pub is_standard_library: bool,
    pub main_environment: Box<Environment>,
    pub files: Vec<FileRunner>,
    pub flattened_export_file: Option<FileId>,
    pub exports: HashMap<String, ExportEntry>,
    pub run_targets: Vec<ImportTarget>,
    pub run_target_lines: HashMap<ImportTarget, LineFile>,
    pub config_imports: Vec<ConfigImport>,
    pub imports: Vec<ModuleId>,
    pub status: ModuleStatus,
    pub execution_mode: ExecutionMode,
    pub strictly_verified: bool,
}

impl ModuleRunner {
    pub fn new(
        id: ModuleId,
        module_name: String,
        module_root_path: String,
        main_file_path: String,
        hierarchy: ProjectHierarchy,
        parent_module_id: Option<ModuleId>,
        status: ModuleStatus,
    ) -> Self {
        ModuleRunner {
            id,
            module_name,
            module_root_path,
            main_file_path,
            hierarchy,
            parent_module_id,
            is_standard_library: false,
            main_environment: Box::new(Environment::new_empty_env()),
            files: vec![],
            flattened_export_file: None,
            exports: HashMap::new(),
            run_targets: vec![],
            run_target_lines: HashMap::new(),
            config_imports: vec![],
            imports: vec![],
            status,
            execution_mode: ExecutionMode::Verified,
            strictly_verified: false,
        }
    }

    pub fn create_exported_file(&mut self, source_path: String, canonical_name: String) -> FileId {
        let id = FileId(self.files.len());
        self.files
            .push(FileRunner::new(id, source_path, canonical_name));
        id
    }

    pub fn file_id_by_source_path(&self, source_path: &str) -> Option<FileId> {
        self.files
            .iter()
            .find(|file| file.source_path == source_path)
            .map(|file| file.id)
    }

    pub fn file(&self, id: FileId) -> Option<&FileRunner> {
        self.files.get(id.0)
    }

    pub fn file_mut(&mut self, id: FileId) -> Option<&mut FileRunner> {
        self.files.get_mut(id.0)
    }

    pub fn record_import(&mut self, module_id: ModuleId) {
        if !self.imports.contains(&module_id) {
            self.imports.push(module_id);
        }
    }
}
