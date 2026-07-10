use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileEnvId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileLoadMode {
    Run,
    Trust,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FileEnvironmentKind {
    Ordinary,
    Exported,
}

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
    Stopped,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ImportTarget {
    File {
        module_id: ModuleId,
        file_id: FileEnvId,
    },
    Module(ModuleId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportEntry {
    File { name: String, file_id: FileEnvId },
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
pub struct FileEnvironment {
    pub id: FileEnvId,
    pub source_path: String,
    pub mode: FileLoadMode,
    pub kind: FileEnvironmentKind,
    pub canonical_name: Option<String>,
    pub environment: Box<Environment>,
    pub local_imports: HashMap<String, ImportTarget>,
    pub status: FileStatus,
}

impl FileEnvironment {
    pub fn new(id: FileEnvId, source_path: String, mode: FileLoadMode) -> Self {
        FileEnvironment {
            id,
            source_path,
            mode,
            kind: FileEnvironmentKind::Ordinary,
            canonical_name: None,
            environment: Box::new(Environment::new_empty_env()),
            local_imports: HashMap::new(),
            status: FileStatus::Loading,
        }
    }

    pub fn new_exported(id: FileEnvId, source_path: String, canonical_name: String) -> Self {
        FileEnvironment {
            id,
            source_path,
            mode: FileLoadMode::Run,
            kind: FileEnvironmentKind::Exported,
            canonical_name: Some(canonical_name),
            environment: Box::new(Environment::new_empty_env()),
            local_imports: HashMap::new(),
            status: FileStatus::Unloaded,
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
    pub file_environments: Vec<FileEnvironment>,
    pub exports: HashMap<String, ExportEntry>,
    pub main_local_imports: HashMap<String, ImportTarget>,
    pub imports: Vec<ModuleId>,
    pub status: ModuleStatus,
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
            file_environments: vec![],
            exports: HashMap::new(),
            main_local_imports: HashMap::new(),
            imports: vec![],
            status,
        }
    }

    pub fn create_file_environment(
        &mut self,
        source_path: String,
        mode: FileLoadMode,
    ) -> FileEnvId {
        let id = FileEnvId(self.file_environments.len());
        self.file_environments
            .push(FileEnvironment::new(id, source_path, mode));
        id
    }

    pub fn create_exported_file_environment(
        &mut self,
        source_path: String,
        canonical_name: String,
    ) -> FileEnvId {
        let id = FileEnvId(self.file_environments.len());
        self.file_environments.push(FileEnvironment::new_exported(
            id,
            source_path,
            canonical_name,
        ));
        id
    }

    pub fn file_environment(&self, id: FileEnvId) -> Option<&FileEnvironment> {
        self.file_environments.get(id.0)
    }

    pub fn file_environment_mut(&mut self, id: FileEnvId) -> Option<&mut FileEnvironment> {
        self.file_environments.get_mut(id.0)
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
                .file_environment(file_id)
                .and_then(|file| file.local_imports.get(name))
                .copied(),
            ExecutionLayer::Builtin => None,
        }
    }
}
