use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

// Label for the kernel-injected builtin fragment in `ModuleManager` (not a Litex keyword).
pub const BUILTIN_CODE_PATH: &str = "builtin_code";

#[derive(Clone)]
pub struct ImportedModule {
    pub absolute_path: String,
    pub environment: Rc<Environment>,
    pub is_std: bool,
    /// Modules imported while this module was loaded.
    ///
    /// This is not a textual include list for display. It is runtime state used
    /// after `clear`: imports are cached but marked stopped, so reimporting this
    /// module must also reactivate these nested imports. For example, reimporting
    /// `Int` should reactivate the cached `Nat` module that `Int` imports.
    pub import_dependencies: Vec<String>,
}

impl ImportedModule {
    pub fn new(
        absolute_path: String,
        environment: Environment,
        is_std: bool,
        import_dependencies: Vec<String>,
    ) -> Self {
        ImportedModule {
            absolute_path,
            environment: Rc::new(environment),
            is_std,
            import_dependencies,
        }
    }
}

/// Tracks module/import state for one top-level run.
///
/// The entry runtime and all imported-module runtimes hold the same
/// `Rc<RefCell<ModuleManager>>`, so nested imports update the state visible to
/// the original runtime.
#[derive(Clone)]
pub struct ModuleManager {
    pub current_source_path_rc: Rc<str>,
    /// Dependencies collected for modules that are still loading.
    ///
    /// Example: while loading `Int`, the statement `import Nat` is seen before
    /// `Int` can be registered as an `ImportedModule`. We temporarily store
    /// `Int -> Nat` here, then move that list into `ImportedModule.import_dependencies`
    /// when `Int` finishes loading. If loading fails, the import rollback restores
    /// this map with the rest of the module-manager snapshot.
    pub pending_import_dependencies: HashMap<String, Vec<String>>,
    pub loading_import_stack: Vec<(String, String)>,
    pub current_module_path: String,
    pub current_module_name: String,
    pub entry_path_rc: Rc<str>,
    pub imported_modules: HashMap<String, ImportedModule>,
    pub stopped_module: HashSet<String>,
}

impl ModuleManager {
    pub fn new_empty_module_manager(initial_path: &str) -> Self {
        let initial_path_rc: Rc<str> = Rc::from(initial_path);
        ModuleManager {
            current_source_path_rc: initial_path_rc.clone(),
            pending_import_dependencies: HashMap::new(),
            loading_import_stack: vec![],
            current_module_path: String::new(),
            current_module_name: String::new(),
            entry_path_rc: initial_path_rc,
            imported_modules: HashMap::new(),
            stopped_module: HashSet::new(),
        }
    }

    pub fn current_file_path_rc(&self) -> Rc<str> {
        self.current_source_path_rc.clone()
    }

    pub fn validate_imported_module_is_new(
        &self,
        module_name: &str,
        absolute_path: &str,
    ) -> Result<(), String> {
        if self.imported_modules.contains_key(module_name) {
            return Err(format!(
                "module name `{}` has already been used",
                module_name
            ));
        }
        if let Some((used_module_name, _)) = self
            .imported_modules
            .iter()
            .find(|(_, imported)| imported.absolute_path == absolute_path)
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
            .imported_modules
            .iter()
            .find(|(_, imported)| imported.absolute_path == absolute_path)
        {
            return Err(format!(
                "module path `{}` has already been imported as module name `{}`",
                absolute_path, used_module_name
            ));
        }
        Ok(false)
    }

    pub fn begin_loading_import(
        &mut self,
        module_name: &str,
        absolute_path: &str,
    ) -> Result<(), String> {
        if let Some(cycle_start_index) = self
            .loading_import_stack
            .iter()
            .position(|(_, loading_path)| loading_path == absolute_path)
        {
            let mut cycle_names = self.loading_import_stack[cycle_start_index..]
                .iter()
                .map(|(loading_name, _)| loading_name.clone())
                .collect::<Vec<String>>();
            cycle_names.push(module_name.to_string());
            return Err(format!("cyclic import: {}", cycle_names.join(" -> ")));
        }

        if self
            .loading_import_stack
            .iter()
            .any(|(loading_name, _)| loading_name == module_name)
        {
            return Err(format!(
                "module name `{}` is already being imported",
                module_name
            ));
        }

        self.loading_import_stack
            .push((module_name.to_string(), absolute_path.to_string()));
        self.pending_import_dependencies
            .entry(module_name.to_string())
            .or_default();
        Ok(())
    }

    pub fn finish_loading_import(&mut self, module_name: &str, absolute_path: &str) {
        if self
            .loading_import_stack
            .last()
            .is_some_and(|(loading_name, loading_path)| {
                loading_name == module_name && loading_path == absolute_path
            })
        {
            self.loading_import_stack.pop();
            return;
        }

        if let Some(index) =
            self.loading_import_stack
                .iter()
                .rposition(|(loading_name, loading_path)| {
                    loading_name == module_name && loading_path == absolute_path
                })
        {
            self.loading_import_stack.remove(index);
        }
    }

    pub fn register_imported_module(
        &mut self,
        module_name: String,
        absolute_path: String,
        environment: Environment,
        is_std: bool,
    ) -> Result<(), String> {
        self.validate_imported_module_is_new(&module_name, &absolute_path)?;
        let import_dependencies = self
            .pending_import_dependencies
            .remove(&module_name)
            .unwrap_or_default();
        self.imported_modules.insert(
            module_name.clone(),
            ImportedModule::new(absolute_path, environment, is_std, import_dependencies),
        );
        self.stopped_module.remove(&module_name);
        Ok(())
    }

    pub fn record_import_dependency(&mut self, module_name: &str, imported_module_name: &str) {
        if module_name.is_empty() || module_name == imported_module_name {
            return;
        }
        let dependencies = self
            .pending_import_dependencies
            .entry(module_name.to_string())
            .or_default();
        if dependencies
            .iter()
            .any(|existing| existing == imported_module_name)
        {
            return;
        }
        dependencies.push(imported_module_name.to_string());
    }

    pub fn reactivate_imported_module(&mut self, module_name: &str) {
        let mut visited_modules = HashSet::new();
        self.reactivate_imported_module_with_dependencies(module_name, &mut visited_modules);
    }

    fn reactivate_imported_module_with_dependencies(
        &mut self,
        module_name: &str,
        visited_modules: &mut HashSet<String>,
    ) {
        if !visited_modules.insert(module_name.to_string()) {
            return;
        }
        self.stopped_module.remove(module_name);
        let dependencies = match self.imported_modules.get(module_name) {
            Some(imported_module) => imported_module.import_dependencies.clone(),
            None => return,
        };
        for dependency_name in dependencies.iter() {
            self.reactivate_imported_module_with_dependencies(dependency_name, visited_modules);
        }
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
