use super::*;

#[test]
fn matrix_literals_require_positive_row_and_column_counts() {
    let source_code = "[[]] = [[]]";
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("matrix_literal_positive_shape");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded, "zero-column matrix literal must fail");
    assert!(
        run_output.contains("matrix literal must have at least one row and one column"),
        "matrix literal should explain its positive-shape requirement:\n{}",
        run_output
    );
}

#[test]
fn matrix_operators_reject_entries_without_real_arithmetic() {
    let source_code = r#"
forall S set, a, b S:
    [[a]] '+ [[b]] = [[a]] '+ [[b]]
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("matrix_operator_real_entries");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "matrix addition over an arbitrary set must fail"
    );
    assert!(
        run_output.contains("matrix '+ requires entries in R"),
        "matrix addition should report its real-entry requirement:\n{}",
        run_output
    );
}

#[test]
fn real_matrix_operators_have_symbolic_types_and_entry_formulas() {
    run_with_large_stack("real_matrix_operators_have_symbolic_semantics", || {
        let source_code = r#"
forall m, n, p N_pos, A, B matrix(R, m, n), C matrix(R, n, p), c R, i, j N_pos:
    i <= m
    j <= n
    =>:
        A '+ B $in matrix(R, m, n)
        A '- B $in matrix(R, m, n)
        c *' A $in matrix(R, m, n)
        (A '+ B)(i, j) = A(i, j) + B(i, j)
        (A '- B)(i, j) = A(i, j) - B(i, j)
        (c *' A)(i, j) = c * A(i, j)

forall m, n, p N_pos, A matrix(R, m, n), B matrix(R, n, p), i, j N_pos:
    i <= m
    j <= p
    =>:
        A '* B $in matrix(R, m, p)
        (A '* B)(i, j) = sum(1, n, fn(k N_pos: k <= n) R {A(i, k) * B(k, j)})

forall n, k N_pos, A matrix(R, n, n), i, j N_pos:
    i <= n
    j <= n
    =>:
        A '^ k $in matrix(R, n, n)
        A '^ 1 = A
        A '^ (k + 1) = (A '^ k) '* A
        (A '^ 1)(i, j) = A(i, j)

[[1]] '+ [[2]] $in matrix(R, 1, 1)
[[2]] '- [[1]] $in matrix(R, 1, 1)
3 *' [[2]] $in matrix(R, 1, 1)
[[2]] '* [[3]] $in matrix(R, 1, 1)
[[2]] '^ 2 $in matrix(R, 1, 1)
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("real_matrix_operators_have_symbolic_semantics");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "real matrix symbolic semantics failed:\n{}",
            run_output
        );
    });
}

#[test]
fn matrix_operator_shape_errors_remain_explicit() {
    let source_code = "[[1, 2]] '+ [[1]] = [[1, 2]] '+ [[1]]";
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("matrix_operator_shape_error");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded, "mismatched matrix shapes must fail");
    assert!(
        run_output.contains("matrix '+ shapes do not match"),
        "matrix shape failure should be explicit:\n{}",
        run_output
    );
}
