use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

/// Owns every module participating in one top-level Runtime.
///
/// Module runners refer to dependencies by `ModuleId`; they never hold Runtime
/// or runner references. This keeps all cross-module lookup and lifecycle state
/// inside one per-run registry.
#[derive(Clone)]
pub struct ModuleManager {
    pub modules: HashMap<ModuleId, ModuleRunner>,
    pub module_by_name: HashMap<String, ModuleId>,
    pub module_by_path: HashMap<String, ModuleId>,
    pub root_exports: HashMap<String, ImportTarget>,
    pub exported_files_by_name: HashMap<String, ImportTarget>,
    pub exported_file_by_path: HashMap<String, ImportTarget>,
    pub loading_module_stack: Vec<ModuleId>,
    pub next_module_id: usize,
    pub entry_module_id: Option<ModuleId>,
    pub entry_path_rc: Rc<str>,
}

impl ModuleManager {
    pub fn new() -> Self {
        ModuleManager {
            modules: HashMap::new(),
            module_by_name: HashMap::new(),
            module_by_path: HashMap::new(),
            root_exports: HashMap::new(),
            exported_files_by_name: HashMap::new(),
            exported_file_by_path: HashMap::new(),
            loading_module_stack: vec![],
            next_module_id: 0,
            entry_module_id: None,
            entry_path_rc: Rc::from(""),
        }
    }

    pub fn create_entry_module(&mut self, main_file_path: &str) -> ModuleId {
        let id = self.allocate_module_id();
        let module_root_path = module_root_path_for_main_file(main_file_path);
        let runner = ModuleRunner::new(
            id,
            String::new(),
            module_root_path,
            main_file_path.to_string(),
            ProjectHierarchy::Module,
            None,
            ModuleStatus::Loaded,
        );
        self.modules.insert(id, runner);
        self.entry_module_id = Some(id);
        self.entry_path_rc = Rc::from(main_file_path);
        id
    }

    pub fn create_repository_entry_module(
        &mut self,
        module_root_path: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        if self.entry_module_id.is_some() {
            return Err("entry module has already been created".to_string());
        }
        let id = self.allocate_module_id();
        let runner = ModuleRunner::new(
            id,
            String::new(),
            module_root_path.clone(),
            main_file_path.clone(),
            ProjectHierarchy::Module,
            None,
            ModuleStatus::Loaded,
        );
        self.modules.insert(id, runner);
        self.module_by_path.insert(module_root_path, id);
        self.entry_module_id = Some(id);
        self.entry_path_rc = Rc::from(main_file_path);
        Ok(id)
    }

    pub fn create_discovered_module(
        &mut self,
        module_name: String,
        module_root_path: String,
        main_file_path: String,
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
        let runner = ModuleRunner::new(
            id,
            module_name.clone(),
            module_root_path.clone(),
            main_file_path,
            hierarchy,
            parent_module_id,
            ModuleStatus::Discovered,
        );
        self.modules.insert(id, runner);
        self.module_by_name.insert(module_name, id);
        self.module_by_path.entry(module_root_path).or_insert(id);
        Ok(id)
    }

    pub fn create_discovered_standard_module(
        &mut self,
        module_name: String,
        module_root_path: String,
        main_file_path: String,
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

    pub fn register_root_export(
        &mut self,
        name: String,
        target: ImportTarget,
    ) -> Result<(), String> {
        if self.root_exports.insert(name.clone(), target).is_some() {
            return Err(format!("duplicate root export name `{}`", name));
        }
        Ok(())
    }

    pub fn register_exported_file(
        &mut self,
        canonical_name: String,
        source_path: String,
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
        // A source file may be mounted more than once.  Its canonical package
        // name, rather than its physical path, is the public identity.
        self.exported_file_by_path
            .entry(source_path)
            .or_insert(target);
        Ok(())
    }

    pub fn root_export(&self, name: &str) -> Option<ImportTarget> {
        self.root_exports.get(name).copied()
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
            ImportTarget::File { module_id, file_id } => self
                .module(module_id)?
                .file(file_id)?
                .canonical_name
                .as_str()
                .into(),
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

    pub fn module_id_by_name(&self, module_name: &str) -> Option<ModuleId> {
        self.module_by_name.get(module_name).copied()
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

    pub fn record_import_dependency(&mut self, importing: ModuleId, imported: ModuleId) {
        if importing == imported {
            return;
        }
        if let Some(module) = self.modules.get_mut(&importing) {
            module.record_import(imported);
        }
    }

    fn allocate_module_id(&mut self) -> ModuleId {
        let id = ModuleId(self.next_module_id);
        self.next_module_id += 1;
        id
    }
}

fn module_root_path_for_main_file(main_file_path: &str) -> String {
    let path = std::path::Path::new(main_file_path);
    path.parent()
        .unwrap_or_else(|| std::path::Path::new(""))
        .to_string_lossy()
        .into_owned()
}

fn local_reference_suffix(name: &str, local_root: &str) -> Option<String> {
    if name == local_root {
        return Some(String::new());
    }
    name.strip_prefix(local_root)
        .filter(|suffix| suffix.starts_with(MOD_SIGN))
        .map(str::to_string)
}
