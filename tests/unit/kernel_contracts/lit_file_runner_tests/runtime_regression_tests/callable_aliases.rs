use super::*;

#[test]
fn callable_alias_still_checks_application_arity() {
    let source = r#"
have fn f(x R) R = x + 1
let g = f
g(1, 2) = 3
"#;

    let mut runtime = Runtime::new();
    runtime.start_isolated_source("callable_alias_arity_boundary");
    let (results, error) = execute_source(source, &mut runtime);
    let (succeeded, output) = render_run_output(&runtime, &results, &error);

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
