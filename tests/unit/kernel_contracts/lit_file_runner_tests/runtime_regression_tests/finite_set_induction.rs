use super::*;
use crate::test_support::execute_source;

#[test]
fn finite_set_induction_result_retains_exact_local_certificate_identity_and_roles() {
    let source_code = r#"
by induc P:
    ? P = P
    ? from P = {}
    ? induc x, S
"#;
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("finite_set_induction_structured_result");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    assert!(runtime_error.is_none(), "{runtime_error:?}");
    let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByFiniteSetInducStmt(
        result,
    )))] = stmt_results.as_slice()
    else {
        panic!("expected one successful finite-set induction result")
    };
    let verification = result
        .verification
        .as_ref()
        .expect("finite-set induction retains verification");
    let SuccessVerifyByInducProofResult::FiniteSet(proof) = &verification.proof else {
        panic!("expected structured finite-set induction proof")
    };
    assert_eq!(proof.base.assumptions.len(), 2);
    assert_eq!(
        proof
            .base
            .assumptions
            .iter()
            .map(|assumption| assumption.role)
            .collect::<Vec<_>>(),
        vec![
            SuccessVerifyByInducAssumptionRole::ParameterType,
            SuccessVerifyByInducAssumptionRole::BaseCaseEquality,
        ]
    );
    assert_eq!(
        proof
            .step
            .assumptions
            .iter()
            .map(|assumption| assumption.role)
            .collect::<Vec<_>>(),
        vec![
            SuccessVerifyByInducAssumptionRole::ParameterType,
            SuccessVerifyByInducAssumptionRole::ParameterType,
            SuccessVerifyByInducAssumptionRole::FreshInsertionElement,
            SuccessVerifyByInducAssumptionRole::InductionHypothesis,
        ]
    );
    assert_eq!(proof.step.assumptions[3].goal_index, Some(0));
    assert_eq!(proof.base.conclusions.len(), 1);
    assert_eq!(proof.step.conclusions.len(), 1);
    for case in [&proof.base, &proof.step] {
        assert!(
            !case.assumption_infers.store_fact_outputs.is_empty(),
            "case must retain local store effects"
        );
        assert!(
            case.assumption_infers
                .store_fact_outputs
                .iter()
                .all(|output| output.fact_id.is_some()),
            "every retained local store needs an exact FactId"
        );
    }
}

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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source("finite_set_induction_positive");
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                run_succeeded,
                "finite-set induction should establish the universal conclusion:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"kind\": \"ByFiniteSetInducStmt\"")
                    && run_output.contains("\"kind\": \"SuccessVerifyByInducResult\""),
                "finite-set induction should identify its proof rule:\n{}",
                run_output
            );
            assert!(
                run_output.contains("forall _generated_") && run_output.contains("finite_set"),
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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("finite_set_induction_carrier");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "carrier-restricted finite-set induction should establish its conclusion:\n{}",
            run_output
        );
        assert!(
            run_output.contains("_generated_") && run_output.contains("$subset A"),
            "the generated conclusion should expose the carrier restriction:\n{}",
            run_output
        );
    });
}

#[test]
fn finite_set_induction_accepts_bodyless_closed_branches() {
    run_with_large_stack(
        "finite_set_induction_accepts_bodyless_closed_branches",
        || {
            let source_code = r#"
by induc P:
    ? P = P
    ? from P = {}
    ? induc x, S
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source("finite_set_induction_bodyless_closed_branches");
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                run_succeeded,
                "bodyless finite-set induction branches should run their final checks:\n{}",
                run_output
            );
            assert!(
                run_output.contains("? from P = {}\\n")
                    && run_output.contains("? induc x, S")
                    && !run_output.contains("? from P = {}:")
                    && !run_output.contains("? induc x, S:"),
                "bodyless finite-set induction branch headers should omit `:`:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn finite_set_induction_rejects_an_unproved_bodyless_insertion_case() {
    run_with_large_stack(
        "finite_set_induction_rejects_an_unproved_bodyless_insertion_case",
        || {
            let source_code = r#"
abstract_prop finite_set_induction_test(P)
trust $finite_set_induction_test({})

by induc P:
    ? $finite_set_induction_test(P)
    ? from P = {}
    ? induc x, S
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source("finite_set_induction_bodyless_negative");
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

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
