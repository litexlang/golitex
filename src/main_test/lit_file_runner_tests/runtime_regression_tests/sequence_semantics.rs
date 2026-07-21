use super::*;

#[test]
fn finite_sequence_literals_require_positive_length() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("finite_sequence_literal_positive_length");
    let (stmt_results, runtime_error) = run_source_code("[] = []", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded, "empty finite sequence literal must fail");
    assert!(
        run_output.contains("finite sequence literal must have at least one element"),
        "empty sequence should explain its positive-length requirement:\n{}",
        run_output
    );

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("finite_sequence_literal_nonempty");
    let (stmt_results, runtime_error) = run_source_code("[1] $in finite_seq(R, 1)", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "nonempty finite sequence literal should remain valid:\n{}",
        run_output
    );
}
