//! Test-only runtime-state reset support.

use super::*;

impl Runtime {
    /// Rebuild the module registry between independent runner items.
    pub fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        self.module_manager = Box::new(ModuleManager::new());
        self.current_module_id = None;
        self.current_source_id = None;
        self.parse_context = ParseContext::new();
        self.start_virtual_source(VirtualSource::CodeExtraction);
        self.set_current_user_lit_file_path(path.as_str());
    }
}

#[test]
fn isolated_source_registers_the_root_module_file() {
    let mut runtime = Runtime::default();
    runtime.start_virtual_source(VirtualSource::Eval);

    assert!(runtime.module_manager.module(ModuleId::ROOT).is_some());
    assert_eq!(runtime.current_module_id, Some(ModuleId::ROOT));
    assert_eq!(runtime.current_source_id, Some(SourceId(0)));
    let file = runtime
        .module_manager
        .module(ModuleId::ROOT)
        .and_then(|module| module.source(SourceId(0)))
        .expect("isolated source should be registered as a module file");
    assert_eq!(file.display_label(), "eval");
    assert!(matches!(
        file.origin,
        SourcePath::VirtualSource(VirtualSource::Eval)
    ));
}

#[test]
fn changing_the_current_source_path_keeps_current_source_and_registry_in_sync() {
    let mut runtime = Runtime::default();
    runtime.start_virtual_source(VirtualSource::CodeExtraction);
    runtime.set_current_user_lit_file_path("first.lit");

    runtime.set_current_user_lit_file_path("second.lit");

    assert_eq!(runtime.current_module_id, Some(ModuleId::ROOT));
    let file = runtime
        .module_manager
        .module(ModuleId::ROOT)
        .and_then(|module| module.source(SourceId(0)))
        .expect("current source file should remain registered");
    assert_eq!(file.display_label(), "second.lit");
}

#[test]
fn isolated_runner_reset_reinitializes_the_runtime_owned_parse_context() {
    let mut runtime = Runtime::default();
    runtime.start_virtual_source(VirtualSource::CodeExtraction);
    runtime.set_current_user_lit_file_path("first.lit");
    runtime.parse_context.local_binding_scope_depth = 1;

    runtime.reset_for_isolated_runner_item();

    assert!(runtime.parse_context.is_at_root_scope());
}
