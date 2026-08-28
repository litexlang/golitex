//! Test-only runtime-state reset support.

use super::*;

impl Runtime {
    /// Rebuild the module registry between independent runner items.
    pub fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        self.module_manager = Box::new(ModuleManager::new());
        self.execution_stack.clear();
        self.start_isolated_source(path.as_str());
    }
}
