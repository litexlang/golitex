use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

// Label for the kernel-injected builtin fragment in `ModuleManager` (not a Litex keyword).
pub const BUILTIN_CODE_PATH: &str = "builtin_code";

#[derive(Clone)]
pub struct DisplaySourceLabel {
    pub source_kind: String,
    pub source: String,
}

impl DisplaySourceLabel {
    pub fn new(source_kind: &str, source: &str) -> Self {
        DisplaySourceLabel {
            source_kind: source_kind.to_string(),
            source: source.to_string(),
        }
    }
}

#[derive(Clone)]
pub struct ImportedModule {
    pub absolute_path: String,
    pub environment: Rc<Environment>,
    pub is_std: bool,
}

impl ImportedModule {
    pub fn new(absolute_path: String, environment: Environment, is_std: bool) -> Self {
        ImportedModule {
            absolute_path,
            environment: Rc::new(environment),
            is_std,
        }
    }
}

#[derive(Clone)]
pub struct ModuleManager {
    pub run_file_paths: Vec<Rc<str>>,
    pub module_name_and_path_map: HashMap<String, String>,
    pub current_module_path: String,
    pub current_module_name: String,
    pub current_file_index: usize,
    pub entry_path: String,
    pub display_entry_rc: Option<Rc<str>>,
    pub hide_file_paths_in_output: bool,
    pub display_source_labels: HashMap<String, DisplaySourceLabel>,
    pub imported_modules: HashMap<String, ImportedModule>,
    pub stopped_module: HashSet<String>,
}

impl ModuleManager {
    pub fn new_empty_module_manager(initial_path: &str) -> Self {
        ModuleManager {
            run_file_paths: vec![Rc::from(initial_path)],
            module_name_and_path_map: HashMap::new(),
            current_module_path: String::new(),
            current_module_name: String::new(),
            current_file_index: FILE_INDEX_FOR_BUILTIN,
            entry_path: initial_path.to_string(),
            display_entry_rc: None,
            hide_file_paths_in_output: false,
            display_source_labels: HashMap::new(),
            imported_modules: HashMap::new(),
            stopped_module: HashSet::new(),
        }
    }

    pub fn current_file_path_rc(&self) -> Rc<str> {
        self.run_file_paths[self.current_file_index].clone()
    }

    pub fn register_display_source_label(&mut self, path: &str, source_kind: &str, source: &str) {
        self.display_source_labels.insert(
            path.to_string(),
            DisplaySourceLabel::new(source_kind, source),
        );
    }

    pub fn validate_imported_module_is_new(
        &self,
        module_name: &str,
        absolute_path: &str,
    ) -> Result<(), String> {
        if self.module_name_and_path_map.contains_key(module_name)
            || self.imported_modules.contains_key(module_name)
        {
            return Err(format!(
                "module name `{}` has already been used",
                module_name
            ));
        }
        if let Some((used_module_name, _)) = self
            .module_name_and_path_map
            .iter()
            .find(|(_, used_path)| used_path.as_str() == absolute_path)
        {
            return Err(format!(
                "module path `{}` has already been imported as module name `{}`",
                absolute_path, used_module_name
            ));
        }
        Ok(())
    }

    pub fn imported_module_can_be_loaded_or_reactivated(
        &self,
        module_name: &str,
        absolute_path: &str,
    ) -> Result<bool, String> {
        if let Some(existing_path) = self.module_name_and_path_map.get(module_name) {
            if existing_path.as_str() == absolute_path {
                return Ok(true);
            }
            return Err(format!(
                "module name `{}` has already been used",
                module_name
            ));
        }
        if let Some(imported_module) = self.imported_modules.get(module_name) {
            if imported_module.absolute_path == absolute_path {
                return Ok(true);
            }
            return Err(format!(
                "module name `{}` has already been used",
                module_name
            ));
        }
        if let Some((used_module_name, _)) = self
            .module_name_and_path_map
            .iter()
            .find(|(_, used_path)| used_path.as_str() == absolute_path)
        {
            return Err(format!(
                "module path `{}` has already been imported as module name `{}`",
                absolute_path, used_module_name
            ));
        }
        Ok(false)
    }

    pub fn register_imported_module(
        &mut self,
        module_name: String,
        absolute_path: String,
        environment: Environment,
        is_std: bool,
    ) -> Result<(), String> {
        self.validate_imported_module_is_new(&module_name, &absolute_path)?;
        self.module_name_and_path_map
            .insert(module_name.clone(), absolute_path.clone());
        self.imported_modules.insert(
            module_name.clone(),
            ImportedModule::new(absolute_path, environment, is_std),
        );
        self.stopped_module.remove(&module_name);
        Ok(())
    }

    pub fn reactivate_imported_module(&mut self, module_name: &str) {
        self.stopped_module.remove(module_name);
    }

    pub fn stop_imported_module(&mut self, module_name: &str) -> Result<(), String> {
        if !self.imported_modules.contains_key(module_name) {
            return Err(format!("module `{}` has not been imported", module_name));
        }
        self.stopped_module.insert(module_name.to_string());
        Ok(())
    }

    pub fn stop_all_imported_modules(&mut self) {
        for module_name in self.imported_modules.keys() {
            self.stopped_module.insert(module_name.clone());
        }
    }

    pub fn imported_module_is_stopped(&self, module_name: &str) -> bool {
        self.stopped_module.contains(module_name)
    }
}
