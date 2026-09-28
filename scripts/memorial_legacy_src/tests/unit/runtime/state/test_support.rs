//! Test-only runtime-state reset support.

use super::*;

fn set_param(runtime: &Runtime, name: &str) -> TypedParameterList {
    TypedParameterList::new(vec![runtime
        .fresh_param_group_with_type(vec![name.to_string()], ParamType::Set(Set::new()))
        .expect("test parameter group should be valid")])
}

impl Runtime {
    /// Rebuild the module registry between independent runner items.
    pub fn reset_for_isolated_runner_item(&mut self) {
        let path = self.current_file_path_rc().to_string();
        let options = self.execution_options;
        *self = Runtime::new_with_virtual_source(options, VirtualSource::CodeExtraction);
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
fn runtime_fact_factories_share_one_monotone_id_sequence() {
    let mut runtime = Runtime::default();
    let left: Obj = Number::new("1".to_string()).into();
    let right: Obj = Number::new("2".to_string()).into();
    let line_file = default_line_file();

    let equality = runtime.new_equal_fact(left.clone(), right.clone(), line_file.clone());
    let membership = runtime.new_in_fact(left, right, line_file.clone());
    let conjunction = runtime.new_and_fact(vec![equality.clone().into()], line_file);

    assert_eq!(equality.fact_id.value(), 1);
    assert_eq!(membership.fact_id.value(), 2);
    assert_eq!(conjunction.fact_id.value(), 3);
    assert_eq!(runtime.next_fact_id.get(), 4);
}

#[test]
fn failed_quantifier_construction_consumes_its_reserved_id() {
    let runtime = Runtime::default();
    let inner = runtime
        .new_forall_fact(
            set_param(&runtime, "x"),
            vec![],
            vec![],
            default_line_file(),
        )
        .expect("inner forall should be valid");

    let failed = runtime.new_forall_fact(
        set_param(&runtime, "x"),
        vec![inner.into()],
        vec![],
        default_line_file(),
    );
    assert!(failed.is_err());
    assert_eq!(runtime.next_fact_id.get(), 3);
}

#[test]
fn cloning_a_fact_preserves_its_id_without_advancing_runtime() {
    let runtime = Runtime::default();
    let first = runtime.new_equal_fact(
        Number::new("1".to_string()).into(),
        Number::new("2".to_string()).into(),
        default_line_file(),
    );
    let cloned = first.clone();
    assert_eq!(cloned.fact_id, first.fact_id);
    assert_eq!(runtime.next_fact_id.get(), 2);

    let second = runtime.new_equal_fact(
        Number::new("2".to_string()).into(),
        Number::new("3".to_string()).into(),
        default_line_file(),
    );
    assert_eq!(second.fact_id.value(), first.fact_id.value() + 1);
}

#[test]
fn repository_start_builds_runtime_with_discovery_source() {
    let runtime = Runtime::new_for_repository(
        RuntimeOptions::default(),
        RealDirectoryPath::new("/tmp/example"),
        RealFilePath::new("/tmp/example/litex.config"),
    )
    .expect("repository setup should construct the discovery source");

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
    let runtime = Runtime::with_virtual_source(VirtualSource::Eval);

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
    let mut runtime = Runtime::with_virtual_source(VirtualSource::CodeExtraction);
    runtime.set_current_user_lit_file_path("first.lit");

    runtime.set_current_user_lit_file_path("second.lit");

    assert_eq!(runtime.current_module_id, ModuleId::ROOT);
    let file = runtime
        .module_manager
        .module(ModuleId::ROOT)
        .and_then(|module| module.source(SourceId(0)))
        .expect("current source file should remain registered");
    assert_eq!(file.display_label(), "second.lit");
    assert!(matches!(
        &file.origin,
        SourcePath::RealFilePath(path) if path.to_string() == "second.lit"
    ));
    assert_eq!(runtime.current_file_path_rc().as_ref(), "second.lit");
}
