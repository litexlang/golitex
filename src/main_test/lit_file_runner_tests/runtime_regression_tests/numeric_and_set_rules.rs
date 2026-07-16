use super::*;

#[test]
fn direct_order_semantics_builtin_rules_cover_transitivity_bounds_and_integer_discreteness() {
    run_with_large_stack(
        "direct_order_semantics_builtin_rules_cover_transitivity_bounds_and_integer_discreteness",
        || {
            let source_code = r#"
forall a, b, c R:
    a <= b
    b < c
    =>:
        a < c

forall a, b, c Z:
    a <= b
    b <= c
    =>:
        a <= c

forall a, b R:
    a <= max(a, b)
    b <= max(a, b)
    min(a, b) <= a
    min(a, b) <= b

forall a, b, c R:
    a <= c
    b <= c
    =>:
        max(a, b) <= c

forall a, b, c R:
    c <= a
    c <= b
    =>:
        c <= min(a, b)

forall a, b Z:
    a < b
    =>:
        a + 1 <= b
        a <= b - 1

forall x, n Z:
    x <= n or x >= n + 1

forall x, n Z:
    n <= x
    x < n + 1
    =>:
        x = n
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "direct_order_semantics_builtin_rules_cover_transitivity_bounds_and_integer_discreteness",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "direct order semantics builtin rules failed:\n{}",
                run_output
            );
            for rule in [
                "order: transitivity through a shared ordered numeric middle term",
                "max: each operand is below the binary maximum",
                "min: the binary minimum is below each operand",
                "max: least upper bound of two real operands",
                "min: greatest lower bound of two real operands",
                "integer successor: a < b gives a + 1 <= b",
                "integer predecessor: a < b gives a <= b - 1",
                "or: integer discrete split x <= n or x >= n + 1",
                "integer singleton interval: n <= x < n + 1 gives x = n",
            ] {
                assert!(
                    run_output.contains(rule),
                    "missing builtin provenance `{}`:\n{}",
                    rule,
                    run_output
                );
            }
        },
    );
}

#[test]
fn integer_discrete_split_does_not_apply_to_reals() {
    let source_code = r#"
forall x, n R:
    x <= n or x >= n + 1
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("integer_discrete_split_does_not_apply_to_reals");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "integer discrete split must not be accepted over R:\n{}",
        run_output
    );
}

#[test]
fn pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined() {
    let source_code = r#"
have fn half_power(x R: x >= 0) R = x^(1/2)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined failed:\n{}",
        run_output
    );
}

#[test]
fn zero_to_zero_power_uses_natural_exponent_convention() {
    run_with_large_stack(
        "zero_to_zero_power_uses_natural_exponent_convention",
        || {
            let source_code = r#"
0^0 = 1
eval 0^0

forall a R:
    a^0 = 1

forall a R, m, n N:
    a^(m+n) = a^m * a^n

forall a, b R, n N:
    (a * b)^n = a^n * b^n

forall a Z, n N:
    a^n $in Z

forall a N, n N:
    a^n $in N

forall a N_pos, n N:
    a^n $in N_pos
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "zero_to_zero_power_uses_natural_exponent_convention",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "zero_to_zero_power_uses_natural_exponent_convention failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"evaluation statement\"")
                    && run_output.contains("\"0 ^ 0 = 1\""),
                "eval 0^0 should produce 1:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn zero_base_real_power_still_requires_positive_exponent() {
    let source_code = r#"
forall x R:
    0^x = 0
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "zero_base_real_power_still_requires_positive_exponent",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "zero_base_real_power_still_requires_positive_exponent should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("base and exponent do not satisfy the pow domain"),
        "failure should still come from pow domain checking:\n{}",
        run_output
    );
}

#[test]
fn sqrt_core_builtin_rules() {
    run_with_large_stack("sqrt_core_builtin_rules_large_stack", || {
        let source_code = r#"
sqrt(0) = 0
sqrt(1) = 1
sqrt(4) = 2
sqrt(452) = sqrt(4 * 113)
sqrt(452) = sqrt(4 * 113) = sqrt(4) * sqrt(113) = 2 * sqrt(113)
sqrt(2) $in R
sqrt(3) / 2 $in R

forall x R:
    x >= 0
    =>:
        (sqrt(x))^2 = x

forall x R:
    x > 0
    =>:
        sqrt(x) > 0

forall x, a, b R:
    x >= 0
    a >= 0
    b >= 0
    x = a * b
    =>:
        sqrt(x) = sqrt(a) * sqrt(b)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("sqrt_core_builtin_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "sqrt_core_builtin_rules failed:\n{}",
            run_output
        );
    });
}

#[test]
fn sqrt_order_and_quotient_builtin_rules() {
    run_with_large_stack("sqrt_order_and_quotient_builtin_rules_large_stack", || {
        let source_code = r#"
forall x R:
    x >= 0
    =>:
        sqrt(x) >= 0

forall x, a, b R:
    x >= 0
    a >= 0
    b > 0
    x = a / b
    =>:
        sqrt(x) = sqrt(a) / sqrt(b)

forall a, b R:
    a >= 0
    b >= 0
    a <= b
    =>:
        sqrt(a) <= sqrt(b)

forall a, b R:
    a >= 0
    b >= 0
    a < b
    =>:
        sqrt(a) < sqrt(b)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("sqrt_order_and_quotient_builtin_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "sqrt_order_and_quotient_builtin_rules failed:\n{}",
            run_output
        );
    });
}

#[test]
fn direct_calculation_equality_is_reported_before_weak_order_fallback() {
    run_with_large_stack(
        "direct_calculation_equality_is_reported_before_weak_order_fallback_large_stack",
        || {
            let source_code = "(-1 * sqrt (2)) ^ 2 = 2";

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "direct_calculation_equality_is_reported_before_weak_order_fallback",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "direct_calculation_equality_is_reported_before_weak_order_fallback failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"rule\": \"calculation\""));
            assert!(!run_output.contains("\"rule\": \"equality from a >= b and b >= a\""));
        },
    );
}

#[test]
fn direct_calculation_builtin_rule_output_localizes_to_zh() {
    run_with_large_stack(
        "direct_calculation_builtin_rule_output_localizes_to_zh_large_stack",
        || {
            let source_code = "(-1 * sqrt (2)) ^ 2 = 2";

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "direct_calculation_builtin_rule_output_localizes_to_zh",
            );
            runtime.output_language = OutputLanguage::SimplifiedChinese;

            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "Chinese direct calculation output failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"规则\": \"计算\""));
            assert!(!run_output.contains("\"rule\": \"calculation\""));
        },
    );
}

#[test]
fn known_equality_candidate_uses_rational_expression_simplification() {
    let source_code = r#"
forall a, b R:
    a^2 + a * a + b = 0
    =>:
        0 = 2 * a^2 + b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_equality_candidate_uses_rational_expression_simplification",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known_equality_candidate_uses_rational_expression_simplification failed:\n{}",
        run_output
    );
    assert!(run_output
        .contains("\"rule\": \"exact calculation and rational expression simplification\""));
    assert!(!run_output.contains("\"rule_id\""));
}

#[test]
fn rational_expression_simplification_builtin_rule_output_localizes_to_zh() {
    let source_code = r#"
forall a, b R:
    a^2 + a * a + b = 0
    =>:
        0 = 2 * a^2 + b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "rational_expression_simplification_builtin_rule_output_localizes_to_zh",
    );
    runtime.output_language = OutputLanguage::SimplifiedChinese;

    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "Chinese rational expression simplification output failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"规则\": \"精确计算和有理表达式化简\""));
    assert!(!run_output
        .contains("\"rule\": \"exact calculation and rational expression simplification\""));
}

#[test]
fn builtin_rule_output_hides_internal_complement_helper_name() {
    let source_code = "1 = 1 or 1 != 1";

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "builtin_rule_output_hides_internal_complement_helper_name",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "complementary-or fixture should verify:\n{}",
        run_output
    );
    assert!(run_output.contains("\"rule\": \"complementary facts cover all cases\""));
    assert!(!run_output.contains("\"rule_id\""));
    assert!(
        !run_output.contains("make_reversed"),
        "public builtin rule output should not expose helper names:\n{}",
        run_output
    );
}

#[test]
fn huge_integer_division_returns_error_instead_of_panicking() {
    let source_code = r#"
1 / 99999999999999999999999999999999999999999 = 0
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "huge_integer_division_returns_error_instead_of_panicking",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "oversized division should fail normally instead of verifying:\n{}",
        run_output
    );
}

#[test]
fn quotient_nonzero_from_numerator_nonzero_builtin_rule() {
    let source_code = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
        0 != a / b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "quotient_nonzero_from_numerator_nonzero_builtin_rule",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "quotient_nonzero_from_numerator_nonzero_builtin_rule failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"rule\": \"div not equal zero from numerator nonzero\""));
}

#[test]
fn known_obj_values_store_simplified_fraction_for_nonfinite_decimal() {
    let source_code = r#"
have a R
trust a = 1 / 2 / 3

have b R
trust b = 1 / 2

have c R
trust c = 2 / -6

have d R
trust d = 1 / (2 / 3 * 4)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "known_obj_values_store_simplified_fraction_for_nonfinite_decimal",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known_obj_values_store_simplified_fraction_for_nonfinite_decimal failed:\n{}",
        run_output
    );

    let env = &runtime.current_module().main_environment;
    match env.known_obj_values.get("a") {
        Some(KnownObjValue::SimplifiedFraction(div)) => {
            assert_eq!(div.left.to_string(), "1");
            assert_eq!(div.right.to_string(), "6");
        }
        other => panic!(
            "expected a to store SimplifiedFraction(1 / 6), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get("b") {
        Some(KnownObjValue::SimplifiedNumber(number)) => {
            assert_eq!(number.normalized_value, "0.5");
        }
        other => panic!(
            "expected b to store SimplifiedNumber(0.5), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get("c") {
        Some(KnownObjValue::SimplifiedFraction(div)) => {
            assert_eq!(div.left.to_string(), "-1");
            assert_eq!(div.right.to_string(), "3");
        }
        other => panic!(
            "expected c to store SimplifiedFraction(-1 / 3), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get("d") {
        Some(KnownObjValue::SimplifiedNumber(number)) => {
            assert_eq!(number.normalized_value, "0.375");
        }
        other => panic!(
            "expected d to store SimplifiedNumber(0.375), got {:?}",
            other.map(|_| "other value")
        ),
    }
}

#[test]
fn simplified_fraction_known_value_is_used_by_resolve() {
    let source_code = r#"
forall a R:
    a = 1 / 2 / 3
    =>:
        a + 1 / 6 = 1 / 3

forall a R:
    a = 2 / -6
    =>:
        a = -1 / 3

forall a R:
    a = 1 / (2 / 3)
    =>:
        a = 3 / 2

forall a R:
    a = 1 / (2 / 3 * 4)
    =>:
        a = 3 / 8
        a + 1 = 11 / 8
"#;

    let mut runtime = Runtime::new();
    runtime
        .new_file_path_new_env_new_name_scope("simplified_fraction_known_value_is_used_by_resolve");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "simplified_fraction_known_value_is_used_by_resolve failed:\n{}",
        run_output
    );
}

#[test]
fn real_interval_membership_rules() {
    let source_code = r#"
have pair cart(R, R) = (0, 1)
have entries finite_seq(R, 2) = [0, 1]

have I set = '(0, 1)

have a R
trust a $in '(0, 1)
a $in R
0 < a
a < 1

have b R
trust b $in '(0, 1]
0 < b
b <= 1

have c R
trust c $in '[0, 1)
0 <= c
c < 1

have d R
trust d $in '[0, 1]
0 <= d
d <= 1

have e R
trust e $in '(,1)
e $in R
e < 1

have f R
trust f $in '(,1]
f $in R
f <= 1

have g R
trust g $in '(0,)
g $in R
0 < g

have h R
trust h $in '[0,)
h $in R
0 <= h

have x R
trust:
    0 < x
    x <= 1
x $in '(0, 1]

have y R
trust:
    0 <= y
y $in '[0,)

have phi fn(t '(0, 1)) R
phi(a) $in R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("real_interval_membership_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "real_interval_membership_rules failed:\n{}",
        run_output
    );
}

#[test]
fn real_interval_nonempty_and_well_defined_rules() {
    let source_code = r#"
have empty_like set = '[1, 0]

have a, b R
trust:
    a <= b
    a < b

$is_nonempty_set('[a, b])
$is_nonempty_set('(a, b))
$is_nonempty_set('(a, b])
$is_nonempty_set('[a, b))
$is_nonempty_set('(,a))
$is_nonempty_set('(,a])
$is_nonempty_set('(a,))
$is_nonempty_set('[a,))

have x '[a, b]
x $in '[a, b]

have y '(a, b)
y $in '(a, b)

have left '[a,)
left $in '[a,)

have right '(,a)
right $in '(,a)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("real_interval_nonempty_and_well_defined_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "real_interval_nonempty_and_well_defined_rules failed:\n{}",
        run_output
    );
}

#[test]
fn strict_even_power_requires_real_base() {
    run_with_large_stack("strict_even_power_requires_real_base", || {
        let positive_source = r#"
have a R
trust a != 0
0 < a^2
"#;
        let mut positive_runtime = Runtime::new();
        positive_runtime
            .new_file_path_new_env_new_name_scope("strict_even_power_requires_real_base_positive");
        let (positive_results, positive_error) =
            run_source_code(positive_source, &mut positive_runtime);
        let (positive_succeeded, positive_output) = render_run_source_code_output(
            &positive_runtime,
            &positive_results,
            &positive_error,
            false,
        );
        assert!(
            positive_succeeded,
            "strict even powers should retain real bases:\n{}",
            positive_output
        );
        assert!(
            positive_output.contains("0 < a^n for even integer n from a != 0"),
            "strict even-power provenance should remain explicit:\n{}",
            positive_output
        );

        let non_real_source = r#"
have S set
trust S != 0
0 < S^2
"#;
        let mut non_real_runtime = Runtime::new();
        non_real_runtime
            .new_file_path_new_env_new_name_scope("strict_even_power_requires_real_base_non_real");
        let (non_real_results, non_real_error) =
            run_source_code(non_real_source, &mut non_real_runtime);
        let (non_real_succeeded, non_real_output) = render_run_source_code_output(
            &non_real_runtime,
            &non_real_results,
            &non_real_error,
            false,
        );
        assert!(
            !non_real_succeeded,
            "a non-real base must not use strict even-power positivity:\n{}",
            non_real_output
        );
    });
}

#[test]
fn real_power_and_order_builtins_require_real_operands() {
    run_with_large_stack(
        "real_power_and_order_builtins_require_real_operands",
        || {
            let positive_source = r#"
have a, b, c, d, e, f, x R
have n N_pos
trust:
    0 < a
    0 <= a
    not a <= x
    a < b
    c <= d
    d <= c
    3 <= e
    e < 3
    2 < f
0 < a^x
0 <= a^x
0 <= a^n
0 <= a^3
0 <= a^2
a > x
a <= b
a != b
c = d
2 <= e
e < 4
0 < f
"#;
            let mut positive_runtime = Runtime::new();
            positive_runtime.new_file_path_new_env_new_name_scope(
                "real_power_and_order_builtins_require_real_operands_positive",
            );
            let (positive_results, positive_error) =
                run_source_code(positive_source, &mut positive_runtime);
            let (positive_succeeded, positive_output) = render_run_source_code_output(
                &positive_runtime,
                &positive_results,
                &positive_error,
                false,
            );
            assert!(
                positive_succeeded,
                "real power and order builtins should remain available:\n{}",
                positive_output
            );

            for (label, source_code) in [
                (
                    "positive_real_exponent",
                    "have S set\nhave x R\ntrust 0 < S\n0 < S^x",
                ),
                (
                    "nonnegative_real_exponent",
                    "have S set\nhave x R\ntrust 0 < S\n0 <= S^x",
                ),
                (
                    "positive_integer_exponent",
                    "have S set\nhave n N_pos\ntrust 0 <= S\n0 <= S^n",
                ),
                (
                    "literal_integer_exponent",
                    "have S set\ntrust 0 <= S\n0 <= S^3",
                ),
                ("even_exponent", "have S set\n0 <= S^2"),
                (
                    "power_equality",
                    "have S set\ntrust S != 0\ntrust S^2 = 0\nS = 0",
                ),
                (
                    "order_from_negated_complement",
                    "have S, T set\ntrust not S <= T\nS > T",
                ),
                (
                    "negated_order_from_equivalent_order",
                    "have S, T set\ntrust S <= T\nnot S > T",
                ),
                ("strict_to_weak_order", "have S, T set\ntrust S < T\nS <= T"),
                ("numeric_lower_bound", "have S set\ntrust 3 <= S\n2 <= S"),
                ("numeric_upper_bound", "have S set\ntrust S < 3\nS < 4"),
                (
                    "two_sided_weak_order_equality",
                    "have S, T set\ntrust S <= T\ntrust T <= S\nS = T",
                ),
                (
                    "strict_order_not_equal",
                    "have S, T set\ntrust S < T\nS != T",
                ),
                ("numeric_sign_inference", "have S set\ntrust 2 < S\n0 < S"),
                (
                    "flipped_sign_inference",
                    "have S set\ntrust S < 0\n-1 * S >= 0",
                ),
            ] {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(
                    format!(
                        "real_power_and_order_builtins_require_real_operands_{}",
                        label
                    )
                    .as_str(),
                );
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    !run_succeeded,
                    "{} must not accept a non-real carrier:\n{}",
                    label, run_output
                );
            }
        },
    );
}

#[test]
fn real_order_carrier_uses_known_subset_membership_without_forall_recursion() {
    run_with_large_stack(
        "real_order_carrier_uses_known_subset_membership_without_forall_recursion",
        || {
            let source_code = r#"
have A nonempty_set
have x A
trust:
    A $subset N
    x < 1
x <= 1
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "real_order_carrier_uses_known_subset_membership_without_forall_recursion",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "a known A subset N must provide x's real carrier without invoking known forall:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn common_power_equalities_and_order_are_builtin() {
    run_with_large_stack("common_power_equalities_and_order_are_builtin", || {
        let source_code = r#"
forall x Q, n, m N:
    x^n * x^m = x^(n + m)

forall x Q, n, m N:
    (x^n)^m = x^(n * m)

forall x R, n, m N:
    x^(n * m) = (x^n)^m

forall x, y Q, n N:
    (x * y)^n = x^n * y^n

forall x Q, n N_pos:
    x^n = 0
    =>:
        x = 0

forall x, y Q, n N_pos:
    x >= y
    y >= 0
    =>:
        x^n >= y^n
        y^n >= 0

forall x R, n N:
    abs(x^n) = abs(x)^n

forall x Q_nz, n, m Z:
    x^n * x^m = x^(n + m)

forall x Q_nz, n, m Z:
    x^n != 0
    =>:
        (x^n)^m = x^(n * m)

8^(1/3) = 2
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("common_power_equalities_and_order_are_builtin");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "common_power_equalities_and_order_are_builtin failed:\n{}",
            run_output
        );
        assert!(run_output.contains("equality: x^(1/n) = z from x = z^n, n in N_pos, and z >= 0"));
    });
}

#[test]
fn reciprocal_power_root_rule_rejects_negative_even_root() {
    run_with_large_stack(
        "reciprocal_power_root_rule_rejects_negative_even_root",
        || {
            let source_code = r#"
16^(1/2) = -4
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "reciprocal_power_root_rule_rejects_negative_even_root",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "principal root rule should not accept a negative even root:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn union_nonempty_when_either_side_nonempty() {
    let source_code = r#"
$is_nonempty_set(union({1}, {}))
$is_nonempty_set(union({}, {2}))

have A, B set
trust:
    $is_nonempty_set(A)

$is_nonempty_set(union(A, B))

have C, D set
trust:
    $is_nonempty_set(D)

$is_nonempty_set(union(C, D))
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("union_nonempty_when_either_side_nonempty");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "union_nonempty_when_either_side_nonempty failed:\n{}",
        run_output
    );
}

#[test]
fn binary_set_membership_introduction_and_elimination_are_builtin() {
    let source_code = r#"
forall x set, A set, B set:
    x $in A
    x $in B
    =>:
        x $in intersect(A, B)

forall x set, A set, B set:
    x $in A
    not x $in B
    =>:
        x $in set_minus(A, B)

have x, A, B, C, D, E, F, G, H set

trust:
    x $in A
    x $in B
    x $in C
    not x $in D
    x $in intersect(E, F)
    x $in set_minus(G, H)

x $in union(A, H)
x $in intersect(A, B)
x $in set_minus(C, D)

x $in E
x $in F
x $in G
not x $in H
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "binary_set_membership_introduction_and_elimination_are_builtin",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "binary_set_membership_introduction_and_elimination_are_builtin failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("union membership: member of the left side"),
        "union introduction should remain a direct builtin:\n{}",
        run_output
    );
    assert!(
        run_output.contains("intersection membership: member of both sides"),
        "intersection introduction should report its builtin provenance:\n{}",
        run_output
    );
    assert!(
        run_output
            .contains("set-minus membership: member of left side and non-member of right side"),
        "set-minus introduction should report its builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn binary_set_membership_introduction_requires_all_prerequisites() {
    for (label, source_code) in [
        (
            "intersection_missing_right_member",
            r#"
have x, A, B set
trust x $in A
x $in intersect(A, B)
"#,
        ),
        (
            "set_minus_missing_right_non_member",
            r#"
have x, A, B set
trust x $in A
x $in set_minus(A, B)
"#,
        ),
    ] {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            format!("binary_set_membership_introduction_requires_all_prerequisites_{label}")
                .as_str(),
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "{label} must not be accepted without every membership prerequisite:\n{}",
            run_output
        );
    }
}

#[test]
fn union_set_equalities_are_builtin() {
    let source_code = r#"
forall A, B set:
    union(A, B) = union(B, A)

forall A, B, C set:
    union(union(A, B), C) = union(A, union(B, C))

forall A set:
    union(A, A) = A
    union(A, {}) = A
    union({}, A) = A

have A, B, C set
union(A, B) = union(B, A)
union(union(A, B), C) = union(A, union(B, C))
union(A, union(B, C)) = union(union(A, B), C)
union(A, A) = A
union(A, {}) = A
union({}, A) = A
A = union(A, A)
A = union(A, {})
A = union({}, A)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("union_set_equalities_are_builtin");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "union_set_equalities_are_builtin failed:\n{}",
        run_output
    );
}

#[test]
fn common_set_algebra_equalities_are_builtin() {
    let source_code = r#"
forall A, B set:
    intersect(A, B) = intersect(B, A)

forall A, B, C set:
    intersect(intersect(A, B), C) = intersect(A, intersect(B, C))

forall A, B, C set:
    intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))

forall A, B, C set:
    set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))

forall A, B, C set:
    set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))

have A, B, C set
intersect(A, B) = intersect(B, A)
intersect(intersect(A, B), C) = intersect(A, intersect(B, C))
intersect(A, intersect(B, C)) = intersect(intersect(A, B), C)
intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))
union(intersect(A, B), intersect(A, C)) = intersect(A, union(B, C))
set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))
intersect(set_minus(A, B), set_minus(A, C)) = set_minus(A, union(B, C))
set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))
union(set_minus(A, B), set_minus(A, C)) = set_minus(A, intersect(B, C))
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("common_set_algebra_equalities_are_builtin");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "common_set_algebra_equalities_are_builtin failed:\n{}",
        run_output
    );
}

#[test]
fn literal_set_intersection_filtering_is_builtin() {
    let cases = [
        r#"
forall S set, x set:
    x $in S
    =>:
        intersect(S, {x}) = {x}
        {x} = intersect(S, {x})
        intersect({x}, S) = {x}
"#,
        r#"
forall S set, x set, y set:
    x != y
    x $in S
    y $in S
    =>:
        intersect(S, {x, y}) = {x, y}
        intersect({x, y}, S) = {x, y}
"#,
        r#"
forall S set, x set, y set:
    x $in S
    not y $in S
    =>:
        intersect(S, {x, y}) = {x}
        intersect({x, y}, S) = {x}
        x != y
        y != x
"#,
        r#"
forall S set, x set, y set:
    x != y
    not x $in S
    not y $in S
    =>:
        intersect(S, {x, y}) = {}
"#,
        r#"
forall S set, x set, y set, z set:
    x != y
    x != z
    y != z
    x $in S
    not y $in S
    z $in S
    =>:
        intersect(S, {x, y, z}) = {x, z}
"#,
        r#"
forall T set, U set:
    U $subset T
    =>:
        intersect(T, U) = U
        intersect(U, T) = U
"#,
        r#"
forall T set, x1 set, x2 set, x3 set, x4 set:
    x1 != x2
    x1 != x3
    x1 != x4
    x2 != x3
    x2 != x4
    x3 != x4
    x1 $in T
    x2 $in T
    x3 $in T
    x4 $in T
    =>:
        intersect(T, {x1, x2, x3, x4}) = {x1, x2, x3, x4}
        intersect({x1, x2, x3, x4}, T) = {x1, x2, x3, x4}
"#,
    ];

    for (i, source_code) in cases.iter().enumerate() {
        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("literal_set_intersection_filtering_is_builtin");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "literal_set_intersection_filtering_is_builtin case {} failed:\n{}",
            i, run_output
        );
    }
}

#[test]
fn intersection_absorption_and_literal_arity_are_builtin() {
    run_with_large_stack(
        "intersection_absorption_and_literal_arity_are_builtin_large_stack",
        || {
            let cases = [
                r#"
forall T set, U set:
    U $subset T
    =>:
        intersect(T, U) = U
        intersect(U, T) = U
"#,
                r#"
forall T set, x1 set, x2 set, x3 set, x4 set:
    x1 != x2
    x1 != x3
    x1 != x4
    x2 != x3
    x2 != x4
    x3 != x4
    x1 $in T
    x2 $in T
    x3 $in T
    x4 $in T
    =>:
        intersect(T, {x1, x2, x3, x4}) = {x1, x2, x3, x4}
        intersect({x1, x2, x3, x4}, T) = {x1, x2, x3, x4}
"#,
            ];

            for (i, source_code) in cases.iter().enumerate() {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(
                    "intersection_absorption_and_literal_arity_are_builtin",
                );
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

                assert!(
                    run_succeeded,
                    "intersection_absorption_and_literal_arity_are_builtin case {} failed:\n{}",
                    i, run_output
                );
            }
        },
    );
}

#[test]
fn one_sided_interval_literal_rejects_invalid_delimiters() {
    for (source_code, expected_error) in [
        (
            "have a R\nhave bad set = '[a,]",
            "right-unbounded interval must end with `)`",
        ),
        (
            "have a R\nhave bad set = '[,a)",
            "left-unbounded interval must start with `(`",
        ),
        (
            "have a R\nhave bad set = '[,a]",
            "left-unbounded interval must start with `(`",
        ),
        (
            "have a R\nhave bad set = '(a,]",
            "right-unbounded interval must end with `)`",
        ),
        (
            "have bad set = '(,)",
            "interval literal cannot omit both endpoints; use `R`",
        ),
    ] {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "one_sided_interval_literal_rejects_invalid_delimiters",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded);
        assert!(
            run_output.contains(expected_error),
            "unexpected interval literal error output:\n{}",
            run_output
        );
    }
}

#[test]
fn integer_quotient_has_euclidean_contract_and_requires_positive_divisor() {
    let source_code = r#"
forall a Z, d N_pos:
    integer_quotient(a, d) $in Z
    a = d * integer_quotient(a, d) + a % d

forall a Z, m N_pos, q Z, r N:
    r < m
    a = m * q + r
    =>:
        a % m = r

integer_quotient(-7, 3) = -3
-7 % 3 = 2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "integer_quotient_has_euclidean_contract_and_requires_positive_divisor",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "integer quotient Euclidean contract failed:\n{}",
        run_output
    );
    for rule in [
        "equality: Euclidean quotient defining equation a = d * integer_quotient(a, d) + a % d",
        "equality: Euclidean remainder uniqueness from a = m * q + r and 0 <= r < m",
    ] {
        assert!(
            run_output.contains(rule),
            "missing integer quotient builtin provenance `{}`:\n{}",
            rule,
            run_output
        );
    }

    let mut invalid_runtime = Runtime::new();
    invalid_runtime
        .new_file_path_new_env_new_name_scope("integer_quotient_rejects_nonpositive_divisor");
    let (invalid_results, invalid_error) =
        run_source_code("integer_quotient(7, -3) = -2", &mut invalid_runtime);
    let (invalid_succeeded, invalid_output) =
        render_run_source_code_output(&invalid_runtime, &invalid_results, &invalid_error, false);
    assert!(
        !invalid_succeeded,
        "integer quotient must reject a non-positive divisor:\n{}",
        invalid_output
    );
    assert!(
        invalid_output.contains("integer_quotient: divisor `-1 * 3` must be in N_pos"),
        "unexpected integer quotient domain error:\n{}",
        invalid_output
    );
}
