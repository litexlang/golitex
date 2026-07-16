use crate::prelude::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

// Stable synthetic source path for the kernel environment, not a user-loadable module.
pub const KERNEL_PATH: &str = "kernel";

/// Owns every module participating in one top-level Runtime.
///
/// Module runners refer to dependencies by `ModuleId`; they never hold Runtime
/// or runner references. This keeps all cross-module lookup and lifecycle state
/// inside one per-run registry.
#[derive(Clone)]
pub struct ModuleManager {
    pub builtin_environment: Box<Environment>,
    pub modules: HashMap<ModuleId, ModuleRunner>,
    pub module_by_name: HashMap<String, ModuleId>,
    /// Standard-library modules loaded for this runtime.  Their names share
    /// the module lookup table but are tracked separately so `import std ...`
    /// cannot be confused with a project import.
    pub std_module_names: HashSet<String>,
    pub module_by_path: HashMap<String, ModuleId>,
    pub root_exports: HashMap<String, ImportTarget>,
    pub exported_files_by_name: HashMap<String, ImportTarget>,
    pub exported_file_by_path: HashMap<String, ImportTarget>,
    pub loading_import_stack: Vec<ModuleId>,
    pub next_module_id: usize,
    pub entry_module_id: Option<ModuleId>,
    pub entry_path_rc: Rc<str>,
}

impl ModuleManager {
    pub fn new(initial_path: &str) -> Self {
        ModuleManager {
            builtin_environment: Box::new(Environment::new_empty_env()),
            modules: HashMap::new(),
            module_by_name: HashMap::new(),
            std_module_names: HashSet::new(),
            module_by_path: HashMap::new(),
            root_exports: HashMap::new(),
            exported_files_by_name: HashMap::new(),
            exported_file_by_path: HashMap::new(),
            loading_import_stack: vec![],
            next_module_id: 0,
            entry_module_id: None,
            entry_path_rc: Rc::from(initial_path),
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
            ModuleStatus::Discovered,
        );
        self.modules.insert(id, runner);
        self.module_by_name.insert(module_name, id);
        self.module_by_path.entry(module_root_path).or_insert(id);
        Ok(id)
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

    pub fn module(&self, id: ModuleId) -> Option<&ModuleRunner> {
        self.modules.get(&id)
    }

    pub fn module_mut(&mut self, id: ModuleId) -> Option<&mut ModuleRunner> {
        self.modules.get_mut(&id)
    }

    pub fn module_id_by_name(&self, module_name: &str) -> Option<ModuleId> {
        self.module_by_name.get(module_name).copied()
    }

    pub fn is_std_module_name(&self, module_name: &str) -> bool {
        self.std_module_names.contains(module_name)
    }

    pub fn is_std_module_id(&self, module_id: ModuleId) -> bool {
        let Some(module) = self.module(module_id) else {
            return false;
        };
        self.std_module_names.iter().any(|std_name| {
            module.module_name == *std_name
                || module
                    .module_name
                    .strip_prefix(std_name)
                    .is_some_and(|suffix| suffix.starts_with(MOD_SIGN))
        })
    }

    pub fn register_std_module(
        &mut self,
        module_name: String,
        module_root_path: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        if self.root_exports.contains_key(&module_name) {
            return Err(format!(
                "std module name `{}` is reserved and conflicts with a project root export",
                module_name
            ));
        }
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
            ModuleStatus::Loading,
        );
        self.modules.insert(id, runner);
        self.module_by_name.insert(module_name.clone(), id);
        self.module_by_path.entry(module_root_path).or_insert(id);
        self.std_module_names.insert(module_name);
        self.loading_import_stack.push(id);
        Ok(id)
    }

    pub fn create_discovered_std_module(
        &mut self,
        module_name: String,
        module_root_path: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        if self.root_exports.contains_key(&module_name) {
            return Err(format!(
                "std module name `{}` is reserved and conflicts with a project root export",
                module_name
            ));
        }
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
            ModuleStatus::Discovered,
        );
        self.modules.insert(id, runner);
        self.module_by_name.insert(module_name.clone(), id);
        self.module_by_path.entry(module_root_path).or_insert(id);
        self.std_module_names.insert(module_name);
        Ok(id)
    }

    pub fn module_by_import_name(&self, module_name: &str) -> Option<&ModuleRunner> {
        let id = self.module_id_by_name(module_name)?;
        self.module(id)
    }

    pub fn imported_module_can_be_loaded(
        &self,
        module_name: &str,
        absolute_path: &str,
    ) -> Result<Option<ModuleId>, String> {
        if let Some(module_id) = self.module_by_name.get(module_name).copied() {
            let Some(module) = self.modules.get(&module_id) else {
                unreachable!("module name index points to a missing module")
            };
            if module.module_root_path == absolute_path {
                if module.status == ModuleStatus::Loading {
                    let cycle_start_index = self
                        .loading_import_stack
                        .iter()
                        .position(|loading_id| *loading_id == module_id)
                        .unwrap_or(0);
                    let mut cycle_names = self.loading_import_stack[cycle_start_index..]
                        .iter()
                        .filter_map(|loading_id| self.modules.get(loading_id))
                        .map(|loading_module| loading_module.module_name.clone())
                        .collect::<Vec<String>>();
                    cycle_names.push(module_name.to_string());
                    return Err(format!("cyclic import: {}", cycle_names.join(" -> ")));
                }
                return Ok(Some(module_id));
            }
            return Err(format!(
                "module name `{}` has already been used",
                module_name
            ));
        }

        if let Some(module_id) = self.module_by_path.get(absolute_path).copied() {
            let Some(module) = self.modules.get(&module_id) else {
                unreachable!("module path index points to a missing module")
            };
            return Err(format!(
                "module path `{}` has already been imported as module name `{}`",
                absolute_path, module.module_name
            ));
        }

        Ok(None)
    }

    pub fn begin_loading_import(
        &mut self,
        module_name: String,
        module_root_path: String,
        main_file_path: String,
    ) -> Result<ModuleId, String> {
        if let Some(cycle_start_index) = self.loading_import_stack.iter().position(|module_id| {
            self.modules
                .get(module_id)
                .is_some_and(|module| module.module_root_path == module_root_path)
        }) {
            let mut cycle_names = self.loading_import_stack[cycle_start_index..]
                .iter()
                .filter_map(|module_id| self.modules.get(module_id))
                .map(|module| module.module_name.clone())
                .collect::<Vec<String>>();
            cycle_names.push(module_name);
            return Err(format!("cyclic import: {}", cycle_names.join(" -> ")));
        }

        if self.module_by_name.contains_key(&module_name) {
            return Err(format!(
                "module name `{}` has already been used",
                module_name
            ));
        }
        if let Some(existing_id) = self.module_by_path.get(&module_root_path) {
            let existing_name = self
                .modules
                .get(existing_id)
                .map(|module| module.module_name.as_str())
                .unwrap_or("");
            return Err(format!(
                "module path `{}` has already been imported as module name `{}`",
                module_root_path, existing_name
            ));
        }

        let id = self.allocate_module_id();
        let runner = ModuleRunner::new(
            id,
            module_name.clone(),
            module_root_path.clone(),
            main_file_path,
            ModuleStatus::Loading,
        );
        self.modules.insert(id, runner);
        self.module_by_name.insert(module_name, id);
        self.module_by_path.insert(module_root_path, id);
        self.loading_import_stack.push(id);
        Ok(id)
    }

    pub fn finish_loading_import(&mut self, module_id: ModuleId) {
        if let Some(module) = self.modules.get_mut(&module_id) {
            module.status = ModuleStatus::Loaded;
        }
        if self.loading_import_stack.last() == Some(&module_id) {
            self.loading_import_stack.pop();
        } else if let Some(index) = self
            .loading_import_stack
            .iter()
            .rposition(|loading_id| *loading_id == module_id)
        {
            self.loading_import_stack.remove(index);
        }
    }

    pub fn begin_loading_discovered_module(&mut self, module_id: ModuleId) -> Result<(), String> {
        let Some(module) = self.modules.get(&module_id) else {
            return Err("discovered module is missing".to_string());
        };
        if module.status == ModuleStatus::Loading {
            let cycle_start_index = self
                .loading_import_stack
                .iter()
                .position(|loading_id| *loading_id == module_id)
                .unwrap_or(0);
            let mut cycle_names = self.loading_import_stack[cycle_start_index..]
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
        self.loading_import_stack.push(module_id);
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
