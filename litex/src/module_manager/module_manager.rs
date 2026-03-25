use crate::common::defaults::DEFAULT_FIRST_FILE_INDEX_FOR_USER;
use crate::runtime::RuntimeContext;
use std::collections::HashMap;
use std::fmt;

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
            run_file_paths: vec!["builtin".to_string(), entrance_file_path.to_string()],
            module_name_and_path_map: HashMap::new(),
            module_path_and_names_map: HashMap::new(),
            current_module_path: String::new(),
            current_module_name: String::new(),
            current_file_index: DEFAULT_FIRST_FILE_INDEX_FOR_USER,
            entrance_path: entrance_file_path.to_string(),
            imported_module_environments: HashMap::new(),
        }
    }
}

impl<'a> fmt::Display for ModuleManager<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ModuleManager {{")?;
        write!(f, "run_file_paths: {:?}", self.run_file_paths)?;
        write!(
            f,
            "module_name_and_path_map: {:?}",
            self.module_name_and_path_map
        )?;
        write!(
            f,
            "module_path_and_names_map: {:?}",
            self.module_path_and_names_map
        )?;
        write!(f, "current_module_path: {}", self.current_module_path)?;
        write!(f, "current_module_name: {}", self.current_module_name)?;
        write!(f, "entrance_path: {}", self.entrance_path)?;
        write!(
            f,
            "imported_module_environments: {:?}",
            self.imported_module_environments
                .keys()
                .collect::<Vec<&String>>()
        )?;
        write!(f, "current_file_index: {}", self.current_file_index)?;
        write!(f, "}}")
    }
}
