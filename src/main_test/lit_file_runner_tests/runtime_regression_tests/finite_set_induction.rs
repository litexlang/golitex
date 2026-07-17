use super::*;

#[test]
fn finite_set_induction_checks_empty_and_insertion_cases() {
    run_with_large_stack(
        "finite_set_induction_checks_empty_and_insertion_cases",
        || {
            let source_code = r#"
abstract_prop finite_set_induction_test(P)
trust $finite_set_induction_test({})
trust forall x set, S finite_set:
    not x $in S
    $finite_set_induction_test(S)
    =>:
        $finite_set_induction_test(union({x}, S))

by induc P:
    ? $finite_set_induction_test(P)
    ? from P = {}:
        $finite_set_induction_test({})
    ? induc x, S:
        $finite_set_induction_test(S)
        $finite_set_induction_test(union({x}, S))

$finite_set_induction_test({1, 2})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("finite_set_induction_positive");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "finite-set induction should establish the universal conclusion:\n{}",
                run_output
            );
            assert!(
                run_output.contains("by finite-set induction proof"),
                "finite-set induction should identify its proof rule:\n{}",
                run_output
            );
            assert!(
                run_output.contains("forall P finite_set"),
                "finite-set induction should store a finite-set forall fact:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn finite_set_induction_can_use_an_explicit_carrier() {
    run_with_large_stack("finite_set_induction_can_use_an_explicit_carrier", || {
        let source_code = r#"
abstract_prop finite_set_induction_carrier_test(P)
trust $finite_set_induction_carrier_test({})
trust forall A finite_set, x A, S finite_set:
    S $subset A
    not x $in S
    $finite_set_induction_carrier_test(S)
    =>:
        $finite_set_induction_carrier_test(union({x}, S))

have A finite_set
trust A $subset Z

by induc P in A:
    ? $finite_set_induction_carrier_test(P)
    ? from P = {}:
        $finite_set_induction_carrier_test({})
    ? induc x, S:
        $finite_set_induction_carrier_test(S)
        $finite_set_induction_carrier_test(union({x}, S))

$finite_set_induction_carrier_test(A)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_set_induction_carrier");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "carrier-restricted finite-set induction should establish its conclusion:\n{}",
            run_output
        );
        assert!(
            run_output.contains("P $subset A"),
            "the generated conclusion should expose the carrier restriction:\n{}",
            run_output
        );
    });
}

#[test]
fn finite_set_induction_rejects_an_unproved_insertion_case() {
    run_with_large_stack(
        "finite_set_induction_rejects_an_unproved_insertion_case",
        || {
            let source_code = r#"
abstract_prop finite_set_induction_test(P)
trust $finite_set_induction_test({})

by induc P:
    ? $finite_set_induction_test(P)
    ? from P = {}:
        $finite_set_induction_test({})
    ? induc x, S:
        $finite_set_induction_test(S)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("finite_set_induction_negative");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "finite-set induction must reject a missing insertion proof:\n{}",
                run_output
            );
            assert!(
                run_output.contains("insertion step is not proved"),
                "the failed insertion obligation should be named clearly:\n{}",
                run_output
            );
        },
    );
}
