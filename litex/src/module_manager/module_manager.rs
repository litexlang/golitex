use crate::common::defaults::FILE_INDEX_FOR_BUILTIN;
use crate::runtime::RuntimeContext;
use std::collections::HashMap;

pub struct ModuleManager<'a> {
    pub run_file_paths: Vec<String>,
    pub module_name_and_path_map: HashMap<String, String>,
    pub module_path_and_names_map: HashMap<String, Vec<String>>,
    pub current_module_path: String,
    pub current_module_name: String,
    pub current_file_index: usize,
    pub entrance_path: String,
    pub imported_module_environments: HashMap<String, Box<RuntimeContext<'a>>>,
}

impl<'a> ModuleManager<'a> {
    pub fn new_empty_module_manager(entrance_file_path: &str) -> Self {
        ModuleManager {
            run_file_paths: vec![entrance_file_path.to_string()],
            module_name_and_path_map: HashMap::new(),
            module_path_and_names_map: HashMap::new(),
            current_module_path: String::new(),
            current_module_name: String::new(),
            current_file_index: FILE_INDEX_FOR_BUILTIN,
            entrance_path: entrance_file_path.to_string(),
            imported_module_environments: HashMap::new(),
        }
    }

    pub fn new_file_path(&mut self, path: &str) {
        self.run_file_paths.push(path.to_string());
        self.current_file_index += 1;
    }
}
