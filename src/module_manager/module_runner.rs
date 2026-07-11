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
    pub local_imports: HashMap<String, ImportTarget>,
    pub status: FileStatus,
    pub execution_mode: ExecutionMode,
}

impl FileRunner {
    pub fn new(id: FileId, source_path: String, canonical_name: String) -> Self {
        FileRunner {
            id,
            source_path,
            canonical_name,
            environment: Box::new(Environment::new_empty_env()),
            local_imports: HashMap::new(),
            status: FileStatus::Unloaded,
            execution_mode: ExecutionMode::Verified,
        }
    }
}

#[derive(Clone)]
pub struct ModuleRunner {
    pub id: ModuleId,
    pub module_name: String,
    pub module_root_path: String,
    pub main_file_path: String,
    pub is_std: bool,
    pub main_environment: Box<Environment>,
    pub files: Vec<FileRunner>,
    pub exports: HashMap<String, ExportEntry>,
    pub main_local_imports: HashMap<String, ImportTarget>,
    pub imports: Vec<ModuleId>,
    pub status: ModuleStatus,
    pub execution_mode: ExecutionMode,
}

impl ModuleRunner {
    pub fn new(
        id: ModuleId,
        module_name: String,
        module_root_path: String,
        main_file_path: String,
        is_std: bool,
        status: ModuleStatus,
    ) -> Self {
        ModuleRunner {
            id,
            module_name,
            module_root_path,
            main_file_path,
            is_std,
            main_environment: Box::new(Environment::new_empty_env()),
            files: vec![],
            exports: HashMap::new(),
            main_local_imports: HashMap::new(),
            imports: vec![],
            status,
            execution_mode: ExecutionMode::Verified,
        }
    }

    pub fn create_exported_file(&mut self, source_path: String, canonical_name: String) -> FileId {
        let id = FileId(self.files.len());
        self.files
            .push(FileRunner::new(id, source_path, canonical_name));
        id
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

    pub fn local_import_target(&self, layer: ExecutionLayer, name: &str) -> Option<ImportTarget> {
        match layer {
            ExecutionLayer::Main => self.main_local_imports.get(name).copied(),
            ExecutionLayer::File(file_id) => self
                .file(file_id)
                .and_then(|file| file.local_imports.get(name))
                .copied(),
            ExecutionLayer::Builtin => None,
        }
    }
}
