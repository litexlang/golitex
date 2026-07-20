use super::*;

#[test]
fn obtain_body_well_defined_can_use_forall_domain_fact() {
    run_with_large_stack(
        "obtain_body_well_defined_can_use_forall_domain_fact",
        || {
            let source_code = r#"
prop image_like(S, T set, f fn(x S) T, A, B set):
    A $subset S
    forall y B:
        exist a A st {y = f(a)}

claim:
    ? forall S, T set, f fn(x S) T, A, B set, x S:
        A $subset S
        $image_like(S, T, f, A, B)
        f(x) $in B
        =>:
            x = x
    claim:
        ? forall a A:
            a $in S
        a $in S
    obtain a from exist a A st {f(x) = f(a)}
    a $in S
    f(x) = f(a)
    x = x
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "obtain_body_well_defined_can_use_forall_domain_fact",
            );
            runtime.detail_output = true;
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "obtain_body_well_defined_can_use_forall_domain_fact failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"object definition by existence\""),
                "obtain from exist should report the semantic statement type\n{}",
                run_output
            );
            assert_no_legacy_acceptance_field(&run_output, "have by exist");
            assert!(
                !run_output.contains("HaveExistObjStmt"),
                "obtain from exist should not report the legacy statement type\n{}",
                run_output
            );
        },
    );
}

#[test]
fn function_space_membership_uses_same_domain_pointwise_values() {
    run_with_large_stack(
        "function_space_membership_uses_same_domain_pointwise_values",
        || {
            let source_code = r#"
claim:
    ? forall I set, X set, f fn(alpha I) cup({X}):
        forall alpha I:
            f(alpha) $in X
        =>:
            f $in fn(alpha I) X
    forall alpha I:
        f(alpha) $in X
    f $in fn(alpha I) X
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "function_space_membership_uses_same_domain_pointwise_values",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "same-domain pointwise function membership failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_fn_restriction_over_abstract_subset_is_well_defined() {
    run_with_large_stack(
        "anonymous_fn_restriction_over_abstract_subset_is_well_defined_large_stack",
        || {
            let source_code = r#"
forall E2 set, E power_set(E2), f fn(x E2) R:
    fn_range(fn(x E) R {f(x)}) $subset R
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_restriction_over_abstract_subset_is_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "anonymous function restriction over abstract subset failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn restricted_lambda_can_apply_function_on_larger_numeric_interval() {
    run_with_large_stack(
        "restricted_lambda_can_apply_function_on_larger_numeric_interval",
        || {
            let source_code = r#"
have fn piece(x '[1, 3]) R by cases:
    case x < 2: x^2
    case x = 2: 7
    case x > 2: x^3

claim:
    ? forall x '[1, 2):
        fn(x '[1, 2)) R {piece(x)}(x) = fn(x '[1, 2)) R {x^2}(x)
    x < 2
    piece(x) = x^2
    fn(x '[1, 2)) R {piece(x)}(x) = piece(x)
    fn(x '[1, 2)) R {x^2}(x) = x^2
    fn(x '[1, 2)) R {piece(x)}(x) = fn(x '[1, 2)) R {x^2}(x)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "restricted_lambda_can_apply_function_on_larger_numeric_interval",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "restricted lambda should inherit numeric interval bounds:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn casewise_function_definition_requires_a_total_disjoint_partition() {
    run_with_large_stack(
        "casewise_function_definition_requires_a_total_disjoint_partition",
        || {
            let invalid_cases = [
                (
                    "casewise_function_missing_coverage",
                    r#"
have fn f(x R) R by cases:
    case x >= 0: 1
"#,
                    "have fn by cases: cases do not cover the declared domain",
                ),
                (
                    "casewise_function_empty_case_list",
                    r#"
have fn f(x R) R by cases:
"#,
                    "block header missing body",
                ),
                (
                    "casewise_function_overlapping_cases_with_same_value",
                    r#"
have fn f(x R) R by cases:
    case x >= 0: 1
    case x <= 0: 1
"#,
                    "have fn by cases: cases overlap or cannot be proved mutually exclusive",
                ),
                (
                    "casewise_function_overlapping_cases_with_conflicting_values",
                    r#"
have fn f(x R) R by cases:
    case x >= 0: 1
    case x <= 0: 2
"#,
                    "have fn by cases: cases overlap or cannot be proved mutually exclusive",
                ),
            ];

            for (label, source_code, expected_error) in invalid_cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(label);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    !run_succeeded,
                    "{} should reject an invalid case partition:\n{}",
                    label, run_output
                );
                assert!(
                    run_output.contains(expected_error),
                    "{} should report the partition failure:\n{}",
                    label,
                    run_output
                );

                let recovery_source = r#"
have fn f(x R) R by cases:
    case x >= 0: 1
    case x < 0: 2

f(0) = 1
"#;
                let (stmt_results, runtime_error) = run_source_code(recovery_source, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    run_succeeded,
                    "{} should not bind the rejected function name:\n{}",
                    label, run_output
                );
            }

            let domain_relative_source = r#"
have fn only_nonnegative(x R: x >= 0) R by cases:
    case x >= 0: x

only_nonnegative(0) = 0
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("casewise_function_domain_coverage");
            let (stmt_results, runtime_error) =
                run_source_code(domain_relative_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "cases only need to cover the declared function domain:\n{}",
                run_output
            );

            let negated_membership_source = r#"
have fn rational_indicator(x R) R by cases:
    case x $in Q: 1
    case not x $in Q: 0

rational_indicator(0) = 1
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "casewise_function_negated_membership_condition",
            );
            let (stmt_results, runtime_error) =
                run_source_code(negated_membership_source, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "casewise functions should accept a leading negated atomic condition:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_fn_equality_transports_across_propositionally_equal_param_sets() {
    run_with_large_stack(
        "anonymous_fn_equality_transports_across_propositionally_equal_param_sets_large_stack",
        || {
            let source_code = r#"
have fn f(x '[1, 3]) R = x

forall J power_set(R):
    J $subset '[1, 3]
    J = '[1, 2)
    =>:
        fn(x J) R {f(x)} = fn(x '[1, 2)) R {f(x)}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_equality_transports_across_propositionally_equal_param_sets",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "anonymous function equality should transport across equal parameter sets:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_fn_body_can_use_singleton_parameter_equality() {
    run_with_large_stack(
        "anonymous_fn_body_can_use_singleton_parameter_equality_large_stack",
        || {
            let source_code = r#"
have fn ambient(x '[1, 3]) R = x

fn(x {2}) R {ambient(x)} = fn(x {2}) R {ambient(x)}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_body_can_use_singleton_parameter_equality",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "a singleton-domain anonymous function should expose its parameter equality:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn conditional_contribution_family_reindexes_to_equal_finite_sum() {
    run_with_large_stack(
        "conditional_contribution_family_reindexes_to_equal_finite_sum_large_stack",
        || {
            let source_code = r#"
prop synthetic_stieltjes_contribution(J power_set(R), t R):
    exist height R st {t = height}

prop synthetic_ordinary_contribution(J power_set(R), t R):
    exist height R st {t = height}

prop synthetic_contribution_family(P finite_set, c fn(J P) R):
    forall J P:
        J $in power_set(R)
        =>:
            $synthetic_stieltjes_contribution(J, c(J))

thm synthetic_stieltjes_contribution_to_ordinary:
    ? forall J power_set(R), t R:
        $synthetic_stieltjes_contribution(J, t)
        =>:
            $synthetic_ordinary_contribution(J, t)
    obtain height from exist height R st {t = height}
    witness exist height0 R st {t = height0} from height:
        t = height
    $synthetic_ordinary_contribution(J, t)

have P finite_set = {{}}
have fn c(J P) R = 0

claim:
    ? $synthetic_contribution_family(P, c)
    claim:
        ? forall J P:
            J $in power_set(R)
            =>:
                $synthetic_stieltjes_contribution(J, c(J))
        witness exist height R st {c(J) = height} from 0:
            c(J) = 0
        $synthetic_stieltjes_contribution(J, c(J))
    $synthetic_contribution_family(P, c)

claim:
    ? forall J P:
        J $in power_set(R)
        =>:
            $synthetic_ordinary_contribution(J, c(J))
    $synthetic_stieltjes_contribution(J, c(J))
    by thm synthetic_stieltjes_contribution_to_ordinary(J, c(J))
    $synthetic_ordinary_contribution(J, c(J))

claim:
    ? $fn_eq(fn(J P) R {0}, c)
    forall K P:
        fn(J P) R {0}(K) = 0
        c(K) = 0
        fn(J P) R {0}(K) = c(K)
    $fn_eq(fn(J P) R {0}, c)

fn(J P) R {0} = c
finite_set_sum(P, fn(J P) R {0}) = finite_set_sum(P, c)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "conditional_contribution_family_reindexes_to_equal_finite_sum",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "conditional contribution family should reindex through an explicit function equality:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_fn_direct_equality_uses_pointwise_extensionality() {
    run_with_large_stack(
        "anonymous_fn_direct_equality_uses_pointwise_extensionality",
        || {
            let positive_source_code = r#"
fn(x R) R {x} = fn(y R) R {y}

forall f, g fn(x R) R:
    fn(x R) R {f(x) + g(x)} = fn(x R) R {g(x) + f(x)}

forall f, g fn(x R) R:
    fn(x R) R {f(x) + g(x)} = fn(x R) R {fn(y R) R {f(y)}(x) + fn(y R) R {g(y)}(x)}

fn(x R: x > 0) R {x} = fn(y R: y > 0) R {y}
"#;

            let mut positive_runtime = Runtime::new();
            positive_runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_direct_equality_uses_pointwise_extensionality_positive",
            );
            let (positive_stmt_results, positive_runtime_error) =
                run_source_code(positive_source_code, &mut positive_runtime);
            let (positive_run_succeeded, positive_run_output) = render_run_source_code_output(
                &positive_runtime,
                &positive_stmt_results,
                &positive_runtime_error,
                false,
            );
            assert!(
                positive_run_succeeded,
                "anonymous fn direct equality should use pointwise extensionality:\n{}",
                positive_run_output
            );

            let negative_source_code = r#"
fn(x N) R {x} = fn(x R) R {x}
"#;

            let mut negative_runtime = Runtime::new();
            negative_runtime.new_file_path_new_env_new_name_scope(
                "anonymous_fn_direct_equality_uses_pointwise_extensionality_negative",
            );
            let (negative_stmt_results, negative_runtime_error) =
                run_source_code(negative_source_code, &mut negative_runtime);
            let (negative_run_succeeded, negative_run_output) = render_run_source_code_output(
                &negative_runtime,
                &negative_stmt_results,
                &negative_runtime_error,
                false,
            );
            assert!(
                !negative_run_succeeded,
                "anonymous fn direct equality should not ignore domain differences:\n{}",
                negative_run_output
            );
        },
    );
}

#[test]
fn curried_have_fn_equal_unfolds_pointwise() {
    let source_code = r#"
have fn seq_add(a, b seq(R)) fn(k N_pos) R = fn(n N_pos) R {a(n) + b(n)}

forall a, b seq(R), k N_pos:
    seq_add(a, b)(k) = a(k) + b(k)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("curried_have_fn_equal_unfolds_pointwise");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "curried have fn equality should unfold pointwise:\n{}",
        run_output
    );
}

#[test]
fn fn_application_returning_fn_set_verifies_sequence_membership() {
    let source_code = r#"
have fn seq_add(a, b seq(R)) fn(k N_pos) R = fn(n N_pos) R {a(n) + b(n)}

forall a, b seq(R):
    seq_add(a, b) $in seq(R)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "fn_application_returning_fn_set_verifies_sequence_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "function application returning a fn set should verify seq membership:\n{}",
        run_output
    );
}

#[test]
fn set_valued_have_fn_application_unfolds_for_membership() {
    let source_code = r#"
have fn circle(r R_pos) power_set(cart(R, R)) = {x cart(R, R): x[1]^2 + x[2]^2 = r^2}
have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {x cart(R, R): a * x[1] + b * x[2] + c = 0}

(3, 4) $in circle(5)
(2, 2) $in line(1, -1, 0)

forall a, b R:
    a != 0 or b != 0
    =>:
        (0, 0) $in line(a, b, 0)

forall p cart(R, R):
    p $in circle(5)
    =>:
        p[1]^2 + p[2]^2 = 5^2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "set_valued_have_fn_application_unfolds_for_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "set-valued have fn applications should unfold for membership:\n{}",
        run_output
    );
}

#[test]
fn set_valued_have_fn_application_keeps_side_conditions() {
    let source_code = r#"
have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {x cart(R, R): a * x[1] + b * x[2] + c = 0}

(0, 0) $in line(0, 0, 0)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "set_valued_have_fn_application_keeps_side_conditions",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "set-valued have fn unfolding should not bypass argument side conditions:\n{}",
        run_output
    );
}

#[test]
fn unary_numeric_objects_respect_argument_equality() {
    let source_code = r#"
forall x, y R:
    x = y
    =>:
        abs(x) = abs(y)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("unary_numeric_objects_respect_argument_equality");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "unary numeric objects should respect argument equality:\n{}",
        run_output
    );
}

#[test]
fn iterated_operator_equality_uses_fn_eq_for_function_arg() {
    run_with_large_stack(
        "iterated_operator_equality_uses_fn_eq_for_function_arg_large_stack",
        || {
            let positive_source_code = r#"
sum(1, 3, fn(x Z) Z {x}) = sum(1, 3, fn(y Z) Z {y})
product(1, 3, fn(x Z) Z {x}) = product(1, 3, fn(y Z) Z {y})

forall f, g fn(x Z) Z:
    sum(1, 3, fn(x Z) Z {f(x) + g(x)}) = sum(1, 3, fn(y Z) Z {g(y) + f(y)})

forall f, g fn(x Z) Z:
    product(1, 3, fn(x Z) Z {f(x) * g(x)}) = product(1, 3, fn(y Z) Z {g(y) * f(y)})
"#;

            let mut positive_runtime = Runtime::new();
            positive_runtime
                .new_file_path_new_env_new_name_scope("iterated_operator_equality_fn_eq_positive");
            let (positive_stmt_results, positive_runtime_error) =
                run_source_code(positive_source_code, &mut positive_runtime);
            let (positive_run_succeeded, positive_run_output) = render_run_source_code_output(
                &positive_runtime,
                &positive_stmt_results,
                &positive_runtime_error,
                false,
            );
            assert!(
                positive_run_succeeded,
                "sum/product equality should compare function args by fn_eq:\n{}",
                positive_run_output
            );

            let negative_source_code = r#"
product(1, 3, fn(x Z) Z {x}) = product(1, 4, fn(y Z) Z {y})
"#;

            let mut negative_runtime = Runtime::new();
            negative_runtime
                .new_file_path_new_env_new_name_scope("iterated_operator_equality_fn_eq_negative");
            let (negative_stmt_results, negative_runtime_error) =
                run_source_code(negative_source_code, &mut negative_runtime);
            let (negative_run_succeeded, negative_run_output) = render_run_source_code_output(
                &negative_runtime,
                &negative_stmt_results,
                &negative_runtime_error,
                false,
            );
            assert!(
                !negative_run_succeeded,
                "product equality should still require equal ranges:\n{}",
                negative_run_output
            );
        },
    );
}

#[test]
fn finite_sum_order_uses_pointwise_bounds() {
    run_with_large_stack("finite_sum_order_uses_pointwise_bounds_large_stack", || {
        let source_code = r#"
thm finite_series_comparison_test:
    ? forall a, b fn(i Z) R, m, n Z:
        m <= n
        forall i Z:
            m <= i <= n
            =>:
                a(i) <= b(i)
        =>:
            sum(m, n, fn(i Z) R {a(i)}) <= sum(m, n, fn(i Z) R {b(i)})

    sum(m, n, fn(i Z) R {a(i)}) <= sum(m, n, fn(i Z) R {b(i)})

thm finite_series_comparison_n_pos_index_test:
    ? forall a, b fn(i N_pos) R, m, n N_pos:
        m <= n
        forall i N_pos:
            m <= i <= n
            =>:
                a(i) <= b(i)
        =>:
            sum(m, n, fn(i N_pos) R {a(i)}) <= sum(m, n, fn(i N_pos) R {b(i)})

    sum(m, n, fn(i N_pos) R {a(i)}) <= sum(m, n, fn(i N_pos) R {b(i)})

thm finite_series_triangle_test:
    ? forall a fn(i Z) R, m, n Z:
        m <= n
        =>:
            abs(sum(m, n, fn(i Z) R {a(i)})) <= sum(m, n, fn(i Z) R {abs(a(i))})

    abs(sum(m, n, fn(i Z) R {a(i)})) <= sum(m, n, fn(i Z) R {abs(a(i))})

thm finite_series_scalar_mul_test:
    ? forall a fn(i Z) R, c R, m, n Z:
        m <= n
        =>:
            sum(m, n, fn(i Z) R {c * a(i)}) = c * sum(m, n, fn(i Z) R {a(i)})

    sum(m, n, fn(i Z) R {c * a(i)}) = c * sum(m, n, fn(i Z) R {a(i)})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_sum_order_uses_pointwise_bounds");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite sum order should use pointwise bounds:\n{}",
            run_output
        );
    });
}

#[test]
fn iterated_operator_range_order_is_required_for_symbolic_bounds() {
    run_with_large_stack(
        "iterated_operator_range_order_is_required_for_symbolic_bounds_large_stack",
        || {
            let cases = [
                (
                    "sum_symbolic_empty_range",
                    r#"
thm bad_symbolic_empty_sum:
    ? forall a fn(i Z) R, m Z:
        sum(m, m - 1, fn(i Z) R {a(i)}) = 0

    trust:
        sum(m, m - 1, fn(i Z) R {a(i)}) = 0
"#,
                    "sum: cannot verify start <= end for the summation range",
                ),
                (
                    "product_symbolic_empty_range",
                    r#"
thm bad_symbolic_empty_product:
    ? forall a fn(i Z) R, m Z:
        product(m, m - 1, fn(i Z) R {a(i)}) = 1

    trust:
        product(m, m - 1, fn(i Z) R {a(i)}) = 1
"#,
                    "product: cannot verify start <= end for the product range",
                ),
            ];

            for (name, source_code, expected_message) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(name);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

                assert!(
                    !run_succeeded,
                    "{} should reject reversed symbolic bounds:\n{}",
                    name, run_output
                );
                assert!(
                    run_output.contains(expected_message),
                    "{} should report the range-order well-definedness failure:\n{}",
                    name,
                    run_output
                );
            }
        },
    );
}

#[test]
fn nested_iterated_operator_with_positive_index_is_well_defined() {
    run_with_large_stack(
        "nested_iterated_operator_with_positive_index_is_well_defined_large_stack",
        || {
            let source_code = r#"
eval sum(1, 3, fn(x N_pos) N_pos {sum(1, x, fn(y N_pos) N_pos {x + y})})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "nested_iterated_operator_with_positive_index_is_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "nested range sum should be well-defined for positive integer indices:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn builtin_function_properties_verify_and_unfold() {
    run_with_large_stack("builtin_function_properties_verify_and_unfold", || {
        let source_code = r#"
have fn identity_on_three(x {1, 2, 3}) {1, 2, 3} = x

forall x1, x2 {1, 2, 3}:
    identity_on_three(x1) = identity_on_three(x2)
    =>:
        x1 = identity_on_three(x1) = identity_on_three(x2) = x2
$injective({1, 2, 3}, {1, 2, 3}, identity_on_three)

claim:
    ? forall y {1, 2, 3}:
        exist x {1, 2, 3} st {y = identity_on_three(x)}
    y = identity_on_three(y)
    witness exist x {1, 2, 3} st {y = identity_on_three(x)} from y
$surjective({1, 2, 3}, {1, 2, 3}, identity_on_three)
$bijective({1, 2, 3}, {1, 2, 3}, identity_on_three)

thm builtin_injective_unfolds:
    ? forall A, B set, f fn(x A) B, x1, x2 A:
        $injective(A, B, f)
        f(x1) = f(x2)
        =>:
            x1 = x2
    x1 = x2

thm builtin_surjective_unfolds:
    ? forall A, B set, f fn(x A) B, y B:
        $surjective(A, B, f)
        =>:
            exist x A st {y = f(x)}
    exist x A st {y = f(x)}

thm builtin_bijective_unfolds:
    ? forall A, B set, f fn(x A) B:
        $bijective(A, B, f)
        =>:
            $injective(A, B, f)
            $surjective(A, B, f)
    $injective(A, B, f)
    $surjective(A, B, f)
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("builtin_function_properties_verify_and_unfold");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "builtin function properties should verify and expose their definitions:\n{}",
            run_output
        );
        assert!(
            run_output.contains("builtin function-property definition"),
            "function-property verification should expose builtin provenance:\n{}",
            run_output
        );
    });
}

#[test]
fn builtin_function_property_negation_uses_by_contra() {
    run_with_large_stack("builtin_function_property_negation_uses_by_contra", || {
        let source_code = r#"
have fn constant(x {1, 2}) {0} = 0

by contra not $injective({1, 2}, {0}, constant):
    constant(1) = constant(2)
    1 = 2
    impossible 1 = 2
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "builtin_function_property_negation_uses_by_contra",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "a constant map on a two-element source should be proved non-injective by contra:\n{}",
            run_output
        );
    });
}

#[test]
fn finite_source_function_property_rules() {
    run_with_large_stack("finite_source_function_property_rules", || {
        let source_code = r#"
thm finite_injection_preserves_size_onto_range:
    ? forall A finite_set, B set, f fn(x A) B:
        $injective(A, B, f)
        =>:
            finite_set_size(fn_range(f)) = finite_set_size(A)
    finite_set_size(fn_range(f)) = finite_set_size(A)

thm finite_surjection_has_finite_bounded_codomain:
    ? forall A finite_set, B set, f fn(x A) B:
        $surjective(A, B, f)
        =>:
            $is_finite_set(B)
            finite_set_size(B) <= finite_set_size(A)
    $is_finite_set(B)
    finite_set_size(B) <= finite_set_size(A)

thm finite_bijection_preserves_size:
    ? forall A finite_set, B set, f fn(x A) B:
        $bijective(A, B, f)
        =>:
            $is_finite_set(B)
            finite_set_size(A) = finite_set_size(B)
    $is_finite_set(B)
    finite_set_size(A) = finite_set_size(B)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_source_function_property_rules");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite-source function-property rules should verify:\n{}",
            run_output
        );
        for expected_rule in [
            "finite injection has range cardinality equal to its source",
            "finite codomain of a surjection from a finite set",
            "finite surjection bounds codomain cardinality by source cardinality",
            "finite bijection preserves cardinality",
        ] {
            assert!(
                run_output.contains(expected_rule),
                "finite-source verification should expose rule `{}`:\n{}",
                expected_rule,
                run_output
            );
        }
    });
}

#[test]
fn builtin_function_properties_reject_malformed_arguments() {
    let source_code = r#"
$injective({1}, {1}, 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "builtin_function_properties_require_matching_function_signature",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "injective should reject a non-function third argument:\n{}",
        run_output
    );
    assert!(
        run_output.contains("requires sets A and B and a function with type fn(x A) B"),
        "wrong function-property signature should report the required function type:\n{}",
        run_output
    );

    let mismatch_source_code = r#"
have fn mismatched_codomain(x {1}) {2} = 2
$injective({1}, {1}, mismatched_codomain)
"#;
    let mut mismatch_runtime = Runtime::new();
    mismatch_runtime.new_file_path_new_env_new_name_scope(
        "builtin_function_properties_reject_mismatched_codomain",
    );
    let (stmt_results, runtime_error) =
        run_source_code(mismatch_source_code, &mut mismatch_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&mismatch_runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "injective should reject a function with the wrong codomain:\n{}",
        run_output
    );
    assert!(
        run_output.contains("requires sets A and B and a function with type fn(x A) B"),
        "mismatched codomain should report the required function type:\n{}",
        run_output
    );

    let mut arity_runtime = Runtime::new();
    arity_runtime
        .new_file_path_new_env_new_name_scope("builtin_function_properties_reject_wrong_arity");
    let (stmt_results, runtime_error) = run_source_code("$injective({1}, {1})", &mut arity_runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&arity_runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "injective should reject two arguments:\n{}",
        run_output
    );
    assert!(
        run_output.contains("fact `injective` expects 3 argument(s), but got 2"),
        "wrong function-property arity should report the expected argument count:\n{}",
        run_output
    );
}

#[test]
fn finite_surjection_rules_do_not_bootstrap_finiteness_cycle() {
    let source_code = r#"
have A, B set
have f fn(x A) B
have g fn(y B) A
trust $surjective(A, B, f)
trust $surjective(B, A, g)
$is_finite_set(A)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_surjection_rules_do_not_bootstrap_finiteness_cycle",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "cyclic surjections without a finite source must not infer finiteness:\n{}",
        run_output
    );
}

#[test]
fn finite_set_sum_core_rules() {
    run_with_large_stack("finite_set_sum_core_rules", || {
        let source_code = r#"
thm finite_set_sum_in_union_from_left:
    ? forall z set, A set, B set:
        z $in A
        =>:
            z $in union(A, B)
    z $in union(A, B)

thm finite_set_sum_in_union_from_right:
    ? forall z set, A set, B set:
        z $in B
        =>:
            z $in union(A, B)
    z $in union(A, B)

finite_set_sum({1, 2, 3}, fn(x Z) Z {x}) = 1 + 2 + 3
finite_set_sum({}, fn(x Z) Z {x}) = 0
finite_set_sum(1...3, fn(x Z) Z {x}) = sum(1, 3, fn(x Z) Z {x})
have P finite_set = {1, 2}
finite_set_sum(P, fn(x P) R {x}) = 3
finite_set_sum({1, 2}, fn(x Z) Z {x}) $in Z
finite_set_sum({1, 2}, fn(x N_pos) N_pos {x}) $in N_pos

sketch:
    have X finite_set
    have c Z
    finite_set_sum(X, fn(x X) Z {c}) = finite_set_size(X) * c

sketch:
    have X power_set(Z)
    trust $is_finite_set(X)
    finite_set_sum(X, fn(x X) Z {x + 0}) = finite_set_sum(X, fn(x X) Z {x})

thm finite_set_sum_substitution_tmp:
    ? forall X, Y finite_set, f fn(x X) R, g fn(y Y) X:
        $bijective(Y, X, g)
        =>:
            finite_set_sum(X, f) = finite_set_sum(Y, fn(y Y) R {f(g(y))})
    finite_set_sum(X, f) = finite_set_sum(Y, fn(y Y) R {f(g(y))})

thm finite_set_sum_range_matches_series_tmp:
    ? forall a fn(i Z) R, m, n Z:
        m <= n
        =>:
            sum(m, n, fn(i Z) R {a(i)}) = finite_set_sum(m...n, fn(i m...n) R {a(i)})
    sum(m, n, fn(i Z) R {a(i)}) = finite_set_sum(m...n, fn(i m...n) R {a(i)})

thm finite_set_sum_disjoint_union_tmp:
    ? forall X, Y finite_set, f fn(z union(X, Y)) R:
        intersect(X, Y) = {}
        =>:
            finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})
    finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})

thm finite_set_sum_add_tmp:
    ? forall X finite_set, f, g fn(x X) R:
        finite_set_sum(X, fn(x X) R {f(x) + g(x)}) = finite_set_sum(X, f) + finite_set_sum(X, g)
    finite_set_sum(X, fn(x X) R {f(x) + g(x)}) = finite_set_sum(X, f) + finite_set_sum(X, g)

thm finite_set_sum_scalar_mul_tmp:
    ? forall X finite_set, f fn(x X) R, c R:
        finite_set_sum(X, fn(x X) R {c * f(x)}) = c * finite_set_sum(X, f)
    finite_set_sum(X, fn(x X) R {c * f(x)}) = c * finite_set_sum(X, f)

thm finite_set_sum_monotone_tmp:
    ? forall X finite_set, f, g fn(x X) R:
        forall x X:
            f(x) <= g(x)
        =>:
            finite_set_sum(X, f) <= finite_set_sum(X, g)
    finite_set_sum(X, f) <= finite_set_sum(X, g)

thm finite_set_sum_member_le_nonnegative_sum_tmp:
    ? forall X finite_set, f fn(x X) R, x X:
        forall y X:
            f(y) >= 0
        =>:
            f(x) <= finite_set_sum(X, f)
    f(x) <= finite_set_sum(X, f)

thm finite_set_sum_triangle_tmp:
    ? forall X finite_set, f fn(x X) R:
        abs(finite_set_sum(X, f)) <= finite_set_sum(X, fn(x X) R {abs(f(x))})
    abs(finite_set_sum(X, f)) <= finite_set_sum(X, fn(x X) R {abs(f(x))})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_set_sum_core_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite_set_sum core rules should verify:\n{}",
            run_output
        );
    });
}

#[test]
fn restricting_a_function_from_a_union_domain_is_well_defined() {
    run_with_large_stack(
        "restricting_a_function_from_a_union_domain_is_well_defined",
        || {
            let source_code = r#"
thm finite_set_sum_disjoint_union_restriction:
    ? forall X, Y finite_set, f fn(z union(X, Y)) R:
        intersect(X, Y) = {}
        =>:
            finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})
    finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "restricting_a_function_from_a_union_domain_is_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a function on union(X, Y) should restrict to X and Y:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn finite_set_sum_cartesian_product_and_fubini() {
    run_with_large_stack("finite_set_sum_cartesian_product_and_fubini", || {
        let source_code = r#"
thm finite_double_sum_over_cartesian_product_tmp:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)
    finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)

thm finite_double_sum_over_cartesian_product_reversed_tmp:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)
    finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)

thm finite_fubini_tmp:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})})
    finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_set_sum_cartesian_product_and_fubini");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite-set Cartesian-product/Fubini rules should verify:\n{}",
            run_output
        );
    });
}

#[test]
fn finite_set_sum_bijective_enumerations_are_well_defined() {
    run_with_large_stack(
        "finite_set_sum_bijective_enumerations_are_well_defined",
        || {
            let source_code = r#"
template<X finite_set, f fn(x X) R, g fn(i closed_range(1, finite_set_size(X))) X: finite_set_size(X) >= 1, $bijective(closed_range(1, finite_set_size(X)), X, g)>:
    have self_finite_set_sum R = sum(1, finite_set_size(X), fn(i closed_range(1, finite_set_size(X))) R {f(g(i))})

thm finite_set_sum_raw_enumeration_well_defined:
    ? forall X finite_set, f fn(x X) R, g fn(i closed_range(1, finite_set_size(X))) X, h fn(i closed_range(1, finite_set_size(X))) X:
        finite_set_size(X) >= 1
        $bijective(closed_range(1, finite_set_size(X)), X, g)
        $bijective(closed_range(1, finite_set_size(X)), X, h)
        =>:
            sum(1, finite_set_size(X), fn(i closed_range(1, finite_set_size(X))) R {f(g(i))}) = sum(1, finite_set_size(X), fn(i closed_range(1, finite_set_size(X))) R {f(h(i))})
    sum(1, finite_set_size(X), fn(i closed_range(1, finite_set_size(X))) R {f(g(i))}) = sum(1, finite_set_size(X), fn(i closed_range(1, finite_set_size(X))) R {f(h(i))})

thm finite_set_sum_template_enumeration_well_defined:
    ? forall X finite_set, f fn(x X) R, g fn(i closed_range(1, finite_set_size(X))) X, h fn(i closed_range(1, finite_set_size(X))) X:
        finite_set_size(X) >= 1
        $bijective(closed_range(1, finite_set_size(X)), X, g)
        $bijective(closed_range(1, finite_set_size(X)), X, h)
        =>:
            \self_finite_set_sum<X, f, g> = \self_finite_set_sum<X, f, h>
    \self_finite_set_sum<X, f, g> = \self_finite_set_sum<X, f, h>
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "finite_set_sum_bijective_enumerations_are_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "finite_set_sum bijective enumeration rules should verify:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn finite_set_product_core_rules() {
    let source_code = r#"
finite_set_product({2, 3, 4}, fn(x Z) Z {x}) = 2 * 3 * 4
finite_set_product({}, fn(x Z) Z {x}) = 1
finite_set_product(1...3, fn(x Z) Z {x}) = product(1, 3, fn(x Z) Z {x})
finite_set_product({1, 2}, fn(x Z) Z {x}) $in Z
finite_set_product({1, 2}, fn(x N_pos) N_pos {x}) $in N_pos
finite_set_product({}, fn(x N_pos) N_pos {x}) $in N_pos

sketch:
    have X finite_set
    have c R
    finite_set_product(X, fn(x X) R {c}) = c ^ finite_set_size(X)

sketch:
    have X power_set(Z)
    trust $is_finite_set(X)
    finite_set_product(X, fn(x X) Z {x + 0}) = finite_set_product(X, fn(x X) Z {x})

thm finite_set_product_fresh_insertion:
    ? forall x Z, S finite_set:
        S $subset Z
        not x $in S
        =>:
            finite_set_product(union({x}, S), fn(y union({x}, S)) Z {y}) = finite_set_product(S, fn(y S) Z {y}) * x
    finite_set_product(union({x}, S), fn(y union({x}, S)) Z {y}) = finite_set_product(S, fn(y S) Z {y}) * x

thm finite_set_product_remove_member:
    ? forall A finite_set, x A:
        A $subset Z
        =>:
            finite_set_product(A, fn(y A) Z {y}) = finite_set_product(set_minus(A, {x}), fn(y set_minus(A, {x})) Z {y}) * x
    finite_set_product(A, fn(y A) Z {y}) = finite_set_product(set_minus(A, {x}), fn(y set_minus(A, {x})) Z {y}) * x
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("finite_set_product_core_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite_set_product core rules should verify:\n{}",
        run_output
    );
}

#[test]
fn dependent_fn_param_set_uses_previous_arg() {
    run_with_large_stack(
        "dependent_fn_param_set_uses_previous_arg_large_stack",
        || {
            let source_code = r#"
have f fn(n N_pos, x closed_range(1, n)) R
f(3, 2) = f(3, 2)
"#;

            let mut runtime = Runtime::new();
            runtime
                .new_file_path_new_env_new_name_scope("dependent_fn_param_set_uses_previous_arg");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "dependent_fn_param_set_uses_previous_arg failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn fn_return_set_cannot_depend_on_params() {
    let source_code = r#"
have f fn(n N_pos) closed_range(1, n)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("fn_return_set_cannot_depend_on_params");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "dependent return set should fail, but succeeded:\n{}",
        run_output
    );
    assert!(
        run_output.contains("function return set cannot depend on function parameters [n]"),
        "dependent return set failure had unexpected output:\n{}",
        run_output
    );
}

#[test]
fn known_equality_implies_weak_order() {
    let source_code = r#"
have a, b R
trust a = b
a <= b
a >= b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("known_equality_implies_weak_order");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known_equality_implies_weak_order failed:\n{}",
        run_output
    );
}

#[test]
fn known_forall_membership_uses_standard_set_subset_direction() {
    let source_code = r#"
abstract_prop p(x)
have x set
trust:
    forall u set:
        $p(u)
        =>:
            u $in Z
trust $p(x)
x $in Q
x $in R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_membership_uses_standard_set_subset_direction",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall with `u $in Z` should prove broader memberships:\n{}",
        run_output
    );
}

#[test]
fn known_forall_membership_narrowing_requires_known_fact() {
    let source_code = r#"
abstract_prop p(x)
have x set
trust:
    forall u set:
        $p(u)
        =>:
        u $in R
trust $p(x)
x $in Z
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_membership_narrowing_requires_known_fact",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "`u $in R` should not prove narrower `x $in Z` without a known `x $in Z` fact:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_uses_indexed_function_head() {
    let source_code = r#"
have f fn(x R) R
trust forall a R:
    f(a) = a
f(1) = 1
"#;

    let mut runtime = Runtime::new();
    runtime
        .new_file_path_new_env_new_name_scope("known_forall_equality_uses_indexed_function_head");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "indexed equality-in-forall should prove matching function applications:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_indexes_forall_param_side_as_wildcard() {
    let source_code = r#"
have f fn(x R) R
trust forall a R:
    a = f(a)
1 + 1 = f(1 + 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_equality_indexes_forall_param_side_as_wildcard",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param equality side should match non-atom target sides:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_with_forall_param_function_head_uses_fallback_bucket() {
    let source_code = r#"
have g fn(x R) R
trust forall f fn(x R) R, a R:
    f(a) = a
g(1) = 1
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_equality_with_forall_param_function_head_uses_fallback_bucket",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param function heads should be checked through the fallback equality bucket:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_forall_param_arg_as_wildcard() {
    let source_code = r#"
abstract_prop p(x)
trust forall x R:
    $p(x)
$p(1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_prop_indexes_forall_param_arg_as_wildcard",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param prop arg should match concrete target args through arg-shape index:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_expression_arg_shape() {
    let source_code = r#"
abstract_prop p(x)
trust forall x R:
    $p(x + 1)
$p(1 + 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("known_forall_prop_indexes_expression_arg_shape");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "expression prop args should be indexed by their top-level operator shape:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_multi_arg_shape() {
    let source_code = r#"
abstract_prop p(a, b)
trust forall a, b R:
    $p(a, b + 1)
$p(2, 3 + 1)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("known_forall_prop_indexes_multi_arg_shape");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "multi-arg prop facts should match wildcard and exact arg-shape positions:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_with_forall_param_function_head_uses_fallback_bucket() {
    let source_code = r#"
abstract_prop p(x)
have g fn(x R) R
trust forall f fn(x R) R:
    $p(f(2))
$p(g(2))
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_prop_with_forall_param_function_head_uses_fallback_bucket",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param function heads in prop args should be checked through the fallback bucket:\n{}",
        run_output
    );
}

#[test]
fn known_forall_matches_function_param_application_inside_anonymous_fn_body() {
    let source_code = r#"
abstract_prop p(x)

trust forall f, g fn(x R) R:
    $p(f)
    $p(g)
    =>:
        $p(fn(x R) R {f(x) + g(x)})

claim:
    ? forall a, b, c fn(x R) R:
        $p(a)
        $p(b)
        $p(c)
        =>:
            $p(fn(x R) R {a(x) + (b(x) + c(x))})
    $p(fn(x R) R {b(x) + c(x)})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_matches_function_param_application_inside_anonymous_fn_body",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall should infer g = anonymous fn from g(x) inside the anonymous body:\n{}",
        run_output
    );
}

#[test]
fn known_forall_does_not_infer_function_from_single_point_application() {
    let source_code = r#"
abstract_prop p(x)

trust forall g fn(x R) R:
    $p(fn(x R) R {g(0)})

have h fn(x R) R
$p(fn(x R) R {h(x)})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_does_not_infer_function_from_single_point_application",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "known forall should not infer a whole function from a single point application:\n{}",
        run_output
    );
}

#[test]
fn eval_recursive_algo_memoizes_overlapping_calls() {
    run_with_large_stack(
        "eval_recursive_algo_memoizes_overlapping_calls_large_stack",
        || {
            let source_code = r#"
sketch:
    have fib fn(x R) R

    trust:
        forall x R:
            x = 0
            =>:
                fib(x) = 0

        forall x R:
            x = 1
            =>:
                fib(x) = 1

        forall x R:
            x > 1
            =>:
                fib(x) = fib(x - 1) + fib(x - 2)

    have algo for fib(x):
        case x = 0: 0
        case x = 1: 1
        fib(x - 1) + fib(x - 2)

    eval fib(25)
    fib(25) = 75025
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "eval_recursive_algo_memoizes_overlapping_calls",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "eval_recursive_algo_memoizes_overlapping_calls failed:\n{}",
                run_output
            );
        },
    );
}
