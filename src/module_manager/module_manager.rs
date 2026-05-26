use crate::prelude::*;
use std::collections::HashMap;
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

pub struct ImportedModuleEnvironment {
    pub environment: Environment,
    pub name_scope: HashMap<String, LineFile>,
}

pub struct ModuleManager {
    pub run_file_paths: Vec<Rc<str>>,
    pub module_name_and_path_map: HashMap<String, String>,
    pub module_path_and_names_map: HashMap<String, Vec<String>>,
    pub current_module_path: String,
    pub current_module_name: String,
    pub current_file_index: usize,
    pub entry_path: String,
    /// Same `Rc` as the user entry slot in `run_file_paths` when set (file path, `repl`, `-e`, ...).
    pub display_entry_rc: Option<Rc<str>>,
    pub hide_file_paths_in_output: bool,
    pub display_source_labels: HashMap<String, DisplaySourceLabel>,
    pub imported_module_environments: HashMap<String, Box<ImportedModuleEnvironment>>,
}

impl ModuleManager {
    pub fn new_empty_module_manager(initial_path: &str) -> Self {
        ModuleManager {
            run_file_paths: vec![Rc::from(initial_path)],
            module_name_and_path_map: HashMap::new(),
            module_path_and_names_map: HashMap::new(),
            current_module_path: String::new(),
            current_module_name: String::new(),
            current_file_index: FILE_INDEX_FOR_BUILTIN,
            entry_path: initial_path.to_string(),
            display_entry_rc: None,
            hide_file_paths_in_output: false,
            display_source_labels: HashMap::new(),
            imported_module_environments: HashMap::new(),
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
}
