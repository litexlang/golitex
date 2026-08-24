use super::*;

#[test]
fn fresh_runtime_has_no_preloaded_source_modules() {
    let runtime = Runtime::new();

    assert!(runtime.module_manager.modules.is_empty());
    assert!(runtime.module_manager.module_by_name.is_empty());
}

#[test]
fn non_isolated_source_imports_require_the_terminal_boundary() {
    for source in ["import \"./Demo\" as Demo", "import std basics"] {
        let mut runtime = Runtime::new();
        runtime.start_isolated_source("repl");

        let (_, runtime_error) = run_source_code(source, &mut runtime);

        let runtime_error = runtime_error.expect("non-isolated import should fail");
        assert!(format!("{runtime_error:?}").contains("only available in an isolated REPL"));
        assert!(runtime.module_manager.module_by_name.is_empty());
    }
}

#[test]
fn strict_mode_rejects_user_trust() {
    let mut runtime = Runtime::new();
    runtime.strict_mode = true;
    runtime.start_isolated_source("repl");

    let (_, trust_error) = run_source_code("trust 1 = 1", &mut runtime);
    assert!(trust_error.is_some(), "strict mode must reject user trust");
}
