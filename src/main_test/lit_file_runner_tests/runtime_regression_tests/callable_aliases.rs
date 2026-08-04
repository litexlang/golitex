use super::*;

#[test]
fn stored_equality_transports_callable_shape_for_well_definedness() {
    let source = r#"
have fn f(x R) R = x + 1
let g = f
let h = g
g(1) = 2
h(1) = 2
fn_range(g) = fn_range(f)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("callable_alias_shape_transport");
    let (results, error) = run_source_code(source, &mut runtime);
    let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);

    assert!(
        succeeded,
        "a callable signature should follow a stored equality class:\n{}",
        output
    );
}

#[test]
fn callable_alias_still_checks_application_arity() {
    let source = r#"
have fn f(x R) R = x + 1
let g = f
g(1, 2) = 3
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("callable_alias_arity_boundary");
    let (results, error) = run_source_code(source, &mut runtime);
    let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);

    assert!(
        !succeeded,
        "equality must not bypass the aliased function's arity check:\n{}",
        output
    );
    assert!(
        output.contains("number of args (2) does not match"),
        "the failure should remain localized to function arity:\n{}",
        output
    );
}
