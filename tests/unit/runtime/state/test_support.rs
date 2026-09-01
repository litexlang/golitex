//! Test-only runtime-state reset support.

use super::*;

impl Runtime {
    /// Rebuild the module registry between independent runner items.
    pub fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        self.module_manager = Box::new(ModuleManager::new());
        self.execution_stack.clear();
        self.parse_context = ParseContext::new();
        self.start_isolated_source(path.as_str());
    }
}

#[test]
fn isolated_source_registers_the_root_module_file() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("eval");

    assert!(runtime.module_manager.module(ModuleId::ROOT).is_some());
    let frame = runtime
        .execution_stack
        .last()
        .expect("isolated source frame should exist");
    assert_eq!(frame.module_file_info.module_id, ModuleId::ROOT);
    assert_eq!(frame.module_file_info.file_id, FileId(0));
    assert_eq!(frame.module_file_info.source_path.as_ref(), "eval");
    let file = runtime
        .module_manager
        .module(ModuleId::ROOT)
        .and_then(|module| module.file(FileId(0)))
        .expect("isolated source should be registered as a module file");
    assert_eq!(file.source_path, "eval");
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

#[test]
fn isolated_runner_reset_reinitializes_the_runtime_owned_parse_context() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("first.lit");
    runtime.parse_context.local_binding_scope_depth = 1;

    runtime.reset_for_isolated_runner_item();

    assert!(runtime.parse_context.is_at_root_scope());
}
