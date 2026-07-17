use super::*;

#[test]
fn dense_real_intervals_have_rational_and_real_witnesses_as_builtin_rules() {
    run_with_large_stack(
        "dense_real_intervals_have_rational_and_real_witnesses_as_builtin_rules",
        || {
            let source_code = r#"
have a, b R:
    a < b

have q Q:
    a < q < b

have r R:
    a < r < b
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "dense_real_intervals_have_rational_and_real_witnesses_as_builtin_rules",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "dense real interval witnesses should be builtin:\n{run_output}"
            );
            assert!(
                run_output.contains("exist: rational density in the real line")
                    && run_output.contains("exist: real density by the midpoint principle"),
                "the result should expose both density rules:\n{run_output}"
            );
        },
    );
}

#[test]
fn integer_ranges_and_euclidean_remainders_have_canonical_builtin_rules() {
    run_with_large_stack(
        "integer_ranges_and_euclidean_remainders_have_canonical_builtin_rules",
        || {
            let source_code = r#"
forall x Q:
    exist p, q Z st {q > 0, x = p / q}

forall a, b Z:
    closed_range(a, b) = {x Z: a <= x <= b}

forall a, b Z:
    range(a, b) = {x Z: a <= x < b}

forall a, b Z:
    b != 0
    a % b = 0
    =>:
        exist k Z st {a = k * b}

forall k N_pos:
    k >= 2
    =>:
        1 % k = 1
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "integer_ranges_and_euclidean_remainders_have_canonical_builtin_rules",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "integer range and remainder rules should be builtin:\n{run_output}"
            );
            for rule in [
                "exist: rational representation with positive integer denominator",
                "equality: closed_range is its integer set-builder definition",
                "equality: range is its integer set-builder definition",
                "exist: zero remainder gives an integer multiple of a nonzero modulus",
                "equality: 1 % k = 1 for k >= 2",
            ] {
                assert!(
                    run_output.contains(rule),
                    "missing builtin provenance `{rule}`:\n{run_output}"
                );
            }
        },
    );
}

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
fn addition_sign_rules_are_builtin() {
    run_with_large_stack("addition_sign_rules_are_builtin", || {
        let positive_cases = [
            (
                "strict_negative_left_sum",
                r#"
forall a, b R:
    a < 0
    b <= 0
    =>:
        a + b < 0
"#,
                "a + b < 0 from one negative term and one nonpositive term",
            ),
            (
                "strict_negative_right_sum",
                r#"
forall a, b R:
    a <= 0
    b < 0
    =>:
        a + b < 0
"#,
                "a + b < 0 from one negative term and one nonpositive term",
            ),
            (
                "weak_negative_sum",
                r#"
forall a, b R:
    a <= 0
    b <= 0
    =>:
        a + b <= 0
"#,
                "a + b <= 0 from a <= 0 and b <= 0",
            ),
        ];

        for (name, source_code, expected_reason) in positive_cases {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(name);
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(run_succeeded, "{name} should be builtin:\n{run_output}");
            assert!(
                run_output.contains(expected_reason),
                "{name} should report its addition-sign builtin provenance:\n{run_output}"
            );
        }

        for (name, source_code) in [
            (
                "mixed_sign_sum_is_not_known_negative",
                r#"
forall a, b R:
    a < 0
    0 < b
    =>:
        a + b < 0
"#,
            ),
            (
                "weakly_nonpositive_sum_is_not_known_strictly_negative",
                r#"
forall a, b R:
    a <= 0
    b <= 0
    =>:
        a + b < 0
"#,
            ),
        ] {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(name);
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "{name} must remain unproved without a sufficient sign hypothesis:\n{run_output}"
            );
            assert!(
                run_output.contains("UnknownError"),
                "{name} should remain an unknown comparison:\n{run_output}"
            );
        }
    });
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
fn positive_real_power_addition_is_builtin() {
    run_with_large_stack("positive_real_power_addition_is_builtin", || {
        let cases = [
            (
                "positive_real_power_addition_forward",
                r#"
forall a R_pos, b, c R:
    a^(b + c) = a^b * a^c
"#,
            ),
            (
                "positive_real_power_addition_reverse",
                r#"
forall a R_pos, b, c R:
    a^b * a^c = a^(b + c)
"#,
            ),
            (
                "positive_real_power_addition_rational_exponents",
                r#"
forall x R_pos, q, r Q:
    x^(q + r) = x^q * x^r
"#,
            ),
        ];

        for (name, source_code) in cases {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(name);
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "{name} should be verified directly by the builtin:\n{run_output}"
            );
            assert!(
                run_output.contains(
                    "equality: a^(m+n) = a^m * a^n for real exponents over positive real bases"
                ),
                "{name} should report the positive-real-base builtin provenance:\n{run_output}"
            );
        }
    });
}

#[test]
fn real_exponent_power_addition_requires_positive_base() {
    run_with_large_stack(
        "real_exponent_power_addition_requires_positive_base",
        || {
            let source_code = r#"
forall a R_nz, b, c R:
    a^(b + c) = a^b * a^c
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "real_exponent_power_addition_requires_positive_base",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "a merely nonzero real base must not justify arbitrary real powers:\n{}",
                run_output
            );
            assert!(
                run_output.contains("base and exponent do not satisfy the pow domain"),
                "failure should preserve the real-power domain boundary:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn positive_real_power_of_power_is_builtin() {
    run_with_large_stack("positive_real_power_of_power_is_builtin", || {
        let cases = [
            (
                "positive_real_power_of_power_forward",
                r#"
forall a R_pos, b, c R:
    (a^b)^c = a^(b * c)
"#,
            ),
            (
                "positive_real_power_of_power_reverse",
                r#"
forall a R_pos, b, c R:
    a^(b * c) = (a^b)^c
"#,
            ),
            (
                "positive_real_power_of_power_nth_root",
                r#"
forall x R, n N_pos:
    x > 0
    =>:
        (x^(1 / n))^n = x^((1 / n) * n)
"#,
            ),
        ];

        for (name, source_code) in cases {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(name);
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "{name} should be verified directly by the builtin:\n{run_output}"
            );
            assert!(
                run_output.contains(
                    "equality: (a^m)^n = a^(m*n) for real exponents over positive real bases"
                ),
                "{name} should report the positive-real-base builtin provenance:\n{run_output}"
            );
        }
    });
}

#[test]
fn real_exponent_power_of_power_requires_positive_base() {
    run_with_large_stack(
        "real_exponent_power_of_power_requires_positive_base",
        || {
            let source_code = r#"
((-2)^2)^(1 / 2) = 2
(-2)^(2 * (1 / 2)) = -2
((-2)^2)^(1 / 2) = (-2)^(2 * (1 / 2))
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "real_exponent_power_of_power_requires_positive_base",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "the power-of-power rule must reject a well-defined negative-base counterexample:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"error_type\": \"UnknownError\"")
                    && !run_output.contains("WellDefinedError"),
                "both sides should be well-defined and the false equality itself should fail:\n{}",
                run_output
            );
        },
    );
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

have x, A, B, C, D, E, F, G, H, U, V set

trust:
    x $in A
    x $in B
    x $in C
    not x $in D
    x $in intersect(E, F)
    x $in set_minus(G, H)
    x $in union(U, V)

x $in union(A, H)
x $in intersect(A, B)
x $in set_minus(C, D)

x $in E
x $in F
x $in G
not x $in H
x $in U or x $in V
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
        run_output.contains("\"type\": \"cite disjunction fact\""),
        "union elimination should cite the inferred membership disjunction:\n{}",
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
fn binary_union_elimination_does_not_choose_a_side() {
    for (name, selected_side) in [
        ("binary_union_does_not_choose_left", "x $in A"),
        ("binary_union_does_not_choose_right", "x $in B"),
    ] {
        let source_code = format!(
            r#"
have x, A, B set
trust x $in union(A, B)
{selected_side}
"#
        );

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(name);
        let (stmt_results, runtime_error) = run_source_code(&source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "union elimination must infer only the disjunction, not {selected_side}:\n{run_output}"
        );
        assert!(
            run_output.contains("UnknownError"),
            "the unjustified selected side should remain unknown:\n{run_output}"
        );
    }
}

#[test]
fn empty_half_open_integer_range_is_builtin() {
    run_with_large_stack("empty_half_open_integer_range_is_builtin", || {
        let source_code = r#"
range(0, 0) = {}

forall a, b Z:
    b <= a
    =>:
        not $is_nonempty_set(range(a, b))
        range(a, b) = {}
        {} = range(a, b)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("empty_half_open_integer_range_is_builtin");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "empty half-open integer ranges should be builtin:\n{run_output}"
        );
        assert!(
            run_output.contains("range empty when end le start")
                && run_output.contains("empty set equality from not nonempty"),
            "the result should expose both range-emptiness and empty-set equality provenance:\n{run_output}"
        );
    });
}

#[test]
fn nonempty_half_open_integer_range_is_not_empty() {
    run_with_large_stack("nonempty_half_open_integer_range_is_not_empty", || {
        let source_code = "range(0, 1) = {}";
        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("nonempty_half_open_integer_range_is_not_empty");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "a half-open range with an integer member must not equal the empty set:\n{run_output}"
        );
        assert!(
            run_output.contains("UnknownError"),
            "the false equality should remain unknown:\n{run_output}"
        );
    });
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

#[test]
fn finite_set_size_set_minus_is_a_builtin_rule() {
    run_with_large_stack("finite_set_size_set_minus_is_a_builtin_rule", || {
        let source_code = r#"
forall s, t finite_set:
    finite_set_size(set_minus(s, t)) = finite_set_size(s) - finite_set_size(intersect(s, t))
"#;
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("finite_set_size_set_minus_is_a_builtin_rule");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "finite-set deletion cardinality should be builtin:\n{run_output}"
        );
        assert!(
            run_output.contains("finite set size set minus"),
            "missing finite-set deletion builtin provenance:\n{run_output}"
        );
    });
}

#[test]
fn finite_set_cardinality_interfaces_are_builtin_rules() {
    run_with_large_stack(
        "finite_set_cardinality_interfaces_are_builtin_rules",
        || {
            let source_code = r#"
forall A, B finite_set:
    B $subset A
    =>:
        finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(B)

forall A, B finite_set:
    finite_set_size(union(A, B)) = finite_set_size(A) + finite_set_size(B) - finite_set_size(intersect(A, B))
    finite_set_size(A) = finite_set_size(intersect(A, B)) + finite_set_size(set_minus(A, B))
    finite_set_size(B) = finite_set_size(intersect(A, B)) + finite_set_size(set_minus(B, A))
    finite_set_size(set_diff(A, B)) = finite_set_size(set_minus(A, B)) + finite_set_size(set_minus(B, A))
    finite_set_size(intersect(A, B)) <= finite_set_size(A)
    finite_set_size(union(A, B)) <= finite_set_size(A) + finite_set_size(B)
    finite_set_size(set_diff(A, B)) <= finite_set_size(A) + finite_set_size(B)

forall A, B finite_set:
    A $superset B
    =>:
        finite_set_size(A) >= finite_set_size(B)

forall a, b N:
    a <= b
    =>:
        finite_set_size(closed_range(a, b)) = b - a + 1
        finite_set_size(range(a, b)) = b - a
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "finite_set_cardinality_interfaces_are_builtin_rules",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "finite-set cardinality interfaces should be builtin:\n{run_output}"
            );
            for rule in [
                "finite set size set minus finite subset",
                "finite set size union inclusion exclusion",
                "finite set size partition by intersection and difference",
                "finite set size symmetric difference",
                "finite set size subset le",
                "finite set size union le sum",
                "finite set size set diff le sum",
                "finite set size closed range",
                "finite set size range",
            ] {
                assert!(
                    run_output.contains(rule),
                    "missing finite-set cardinality builtin provenance `{rule}`:\n{run_output}"
                );
            }
        },
    );
}

#[test]
fn finite_set_size_subset_and_integer_interval_cardinalities_are_builtin_rules() {
    let source_code = r#"
forall A, B finite_set:
    A $subset B
    =>:
        finite_set_size(A) <= finite_set_size(B)

forall a, b N:
    a <= b
    =>:
        finite_set_size(closed_range(a, b)) = b - a + 1
        finite_set_size(range(a, b)) = b - a
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_set_size_subset_and_integer_interval_cardinalities_are_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite-set size and integer interval cardinalities should be builtin:\n{run_output}"
    );
    for rule in [
        "finite set size subset le",
        "finite set size closed range",
        "finite set size range",
    ] {
        assert!(
            run_output.contains(rule),
            "missing finite-set cardinality builtin provenance `{rule}`:\n{run_output}"
        );
    }
}

#[test]
fn finite_subset_uses_axiom_matching_and_cyclic_subsets_terminate() {
    run_with_large_stack(
        "finite_subset_uses_axiom_matching_and_cyclic_subsets_terminate",
        || {
            let builtin_only_source = r#"
forall A set, B finite_set:
    A $subset B
    =>:
        $is_finite_set(A)
"#;
            let mut builtin_only_runtime = Runtime::new();
            builtin_only_runtime
                .new_file_path_new_env_new_name_scope("finite_subset_is_not_builtin");
            let (builtin_only_results, builtin_only_error) =
                run_source_code(builtin_only_source, &mut builtin_only_runtime);
            let (builtin_only_succeeded, builtin_only_output) = render_run_source_code_output(
                &builtin_only_runtime,
                &builtin_only_results,
                &builtin_only_error,
                false,
            );

            assert!(
                !builtin_only_succeeded,
                "arbitrary subset finiteness must not be a builtin:\n{builtin_only_output}"
            );
            assert!(
                !builtin_only_output.contains("finite set subset is finite"),
                "removed builtin provenance must not appear:\n{builtin_only_output}"
            );

            let finite_chain_source = r#"
axiom subset_of_finite_set_is_finite:
    ? forall A set, B finite_set:
        A $subset B
        =>:
            $is_finite_set(A)

thm finite_subset_chain:
    ? forall A, B set, C finite_set:
        A $subset B
        B $subset C
        =>:
            $is_finite_set(A)
    by thm subset_of_finite_set_is_finite(B, C)
    $is_finite_set(B)
    by thm subset_of_finite_set_is_finite(A, B)
    $is_finite_set(A)
"#;
            let mut finite_chain_runtime = Runtime::new();
            finite_chain_runtime.new_file_path_new_env_new_name_scope("finite_subset_axiom_chain");
            let (finite_chain_results, finite_chain_error) =
                run_source_code(finite_chain_source, &mut finite_chain_runtime);
            let (finite_chain_succeeded, finite_chain_output) = render_run_source_code_output(
                &finite_chain_runtime,
                &finite_chain_results,
                &finite_chain_error,
                false,
            );

            assert!(
                finite_chain_succeeded,
                "explicit axiom matching should follow a finite subset chain:\n{finite_chain_output}"
            );
            assert!(
                !finite_chain_output.contains("finite set subset is finite"),
                "the finite chain must not use removed builtin provenance:\n{finite_chain_output}"
            );

            let cyclic_source = r#"
axiom subset_of_finite_set_is_finite:
    ? forall A set, B finite_set:
        A $subset B
        =>:
            $is_finite_set(A)

forall A, B set:
    A $subset B
    B $subset A
    =>:
        $is_finite_set(A)
"#;
            let mut cyclic_runtime = Runtime::new();
            cyclic_runtime.new_file_path_new_env_new_name_scope("cyclic_finite_subset_axiom");
            let (cyclic_results, cyclic_error) =
                run_source_code(cyclic_source, &mut cyclic_runtime);
            let (cyclic_succeeded, cyclic_output) = render_run_source_code_output(
                &cyclic_runtime,
                &cyclic_results,
                &cyclic_error,
                false,
            );

            assert!(
                !cyclic_succeeded,
                "cyclic subset assumptions without a finite base must fail normally:\n{cyclic_output}"
            );
            assert!(
                !cyclic_output.contains("finite set subset is finite"),
                "the cycle must not re-enter removed builtin provenance:\n{cyclic_output}"
            );
        },
    );
}

#[test]
fn finite_set_extrema_are_public_source_level_interfaces() {
    let source_code = r#"
import std basics

thm finite_set_extrema_have_defining_properties:
    ? forall S power_set(N), x S:
        $is_finite_set(S)
        $is_nonempty_set(S)
        =>:
            basics::finite_set_max(S) $in S
            x <= basics::finite_set_max(S)
            basics::finite_set_min(S) $in S
            basics::finite_set_min(S) <= x
    by thm basics::finite_set_max_in_set(S)
    by thm basics::finite_set_member_le_max(S, x)
    by thm basics::finite_set_min_in_set(S)
    by thm basics::finite_set_min_le_member(S, x)
"#;
    let mut runtime = Runtime::new();
    runtime.isolated = true;
    runtime.new_file_path_new_env_new_name_scope("finite_set_extrema_public_interfaces");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite-set extrema should be available through public basics theorems:\n{run_output}"
    );
    for theorem_name in [
        "basics::finite_set_max_in_set",
        "basics::finite_set_member_le_max",
        "basics::finite_set_min_in_set",
        "basics::finite_set_min_le_member",
    ] {
        assert!(
            run_output.contains(theorem_name),
            "missing public finite-set extrema theorem `{theorem_name}`:\n{run_output}"
        );
    }
}
