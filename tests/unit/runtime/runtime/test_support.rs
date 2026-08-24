use super::*;

impl Runtime {
    /// Rebuild the module registry between independent runner items.
    pub fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        self.module_manager = Box::new(ModuleManager::new());
        self.execution_stack.clear();
        self.new_file_path_new_env_new_name_scope(path.as_str());
    }
}
