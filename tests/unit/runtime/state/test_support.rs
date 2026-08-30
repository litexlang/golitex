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

#[test]
fn isolated_source_registers_the_root_module_file() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("<-e>");

    assert_eq!(runtime.module_manager.entry_module_id, Some(ModuleId::ROOT));
    let frame = runtime
        .execution_stack
        .last()
        .expect("isolated source frame should exist");
    assert_eq!(frame.module_file_info.module_id, ModuleId::ROOT);
    assert_eq!(frame.module_file_info.file_id, FileId(0));
    assert_eq!(frame.module_file_info.source_path.as_ref(), "<-e>");
    let file = runtime
        .module_manager
        .module(ModuleId::ROOT)
        .and_then(|module| module.file(FileId(0)))
        .expect("isolated source should be registered as a module file");
    assert_eq!(file.source_path, "<-e>");
    assert!(file.is_virtual_source);
}

#[test]
fn changing_the_current_source_path_keeps_frame_and_registry_in_sync() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("first.lit");

    runtime.set_current_user_lit_file_path("second.lit");

    let frame = runtime
        .execution_stack
        .last()
        .expect("isolated source frame should exist");
    assert_eq!(frame.module_file_info.source_path.as_ref(), "second.lit");
    let file = runtime
        .module_manager
        .module(frame.module_file_info.module_id)
        .and_then(|module| module.file(frame.module_file_info.file_id))
        .expect("current source file should remain registered");
    assert_eq!(file.source_path, "second.lit");
}
