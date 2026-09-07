//! Test-only runtime-state reset support.

use super::*;

impl Runtime {
    /// Rebuild the module registry between independent runner items.
    pub fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        self.module_manager = Box::new(ModuleManager::new());
        let source_id = self
            .module_manager
            .create_virtual_root_module(VirtualSource::CodeExtraction);
        self.current_module_id = ModuleId::ROOT;
        self.current_source_id = source_id;
        self.execution_mode = ExecutionMode::RequireVerification;
        self.current_environment_stack.clear();
        self.bootstrap_source_pending = false;
        self.parse_context = ParseContext::new();
        self.set_current_user_lit_file_path(path.as_str());
    }
}

#[test]
fn runtime_constructor_registers_an_active_eval_source() {
    let runtime = Runtime::default();

    assert_eq!(runtime.current_module_id, ModuleId::ROOT);
    assert_eq!(runtime.current_source_id, SourceId(0));
    assert_eq!(runtime.current_file_path_rc().as_ref(), "eval");
    assert_eq!(runtime.current_source().id, SourceId(0));
}

#[test]
fn repository_start_reuses_the_registered_constructor_source() {
    let mut runtime = Runtime::default();

    let module_id = runtime
        .start_repository_run_typed(
            RealDirectoryPath::new("/tmp/example"),
            RealFilePath::new("/tmp/example/litex.config"),
        )
        .expect("repository setup should reuse the constructor source");

    assert_eq!(module_id, ModuleId::ROOT);
    assert_eq!(runtime.current_module_id, ModuleId::ROOT);
    assert_eq!(runtime.current_source_id, SourceId(0));
    assert_eq!(
        runtime.current_file_path_rc().as_ref(),
        "repository-discovery:/tmp/example/litex.config"
    );
    assert!(matches!(
        &runtime.current_module().location,
        ModuleLocation::Repository { .. }
    ));
    assert!(matches!(
        &runtime.current_source().origin,
        SourcePath::VirtualSource(VirtualSource::Named(_))
    ));
}

#[test]
fn isolated_source_registers_the_root_module_file() {
    let mut runtime = Runtime::default();
    runtime.start_virtual_source(VirtualSource::Eval);

    assert!(runtime.module_manager.module(ModuleId::ROOT).is_some());
    assert_eq!(runtime.current_module_id, ModuleId::ROOT);
    assert_eq!(runtime.current_source_id, SourceId(0));
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

    assert_eq!(runtime.current_module_id, ModuleId::ROOT);
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
