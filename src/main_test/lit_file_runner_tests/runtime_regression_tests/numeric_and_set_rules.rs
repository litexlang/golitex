use super::*;

#[test]
fn pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined() {
    let source_code = r#"
have fn half_power(x R: x >= 0) R = x^(1/2)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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
fn builtin_rational_has_unique_reduced_fraction() {
    let source_code = r#"
have q Q

by thm rational_has_unique_reduced_fraction(q)
exist! a Z, b N_pos st {q = a / b, $is_reduced_fraction(a, b)}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("builtin_rational_has_unique_reduced_fraction");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "builtin_rational_has_unique_reduced_fraction failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("unique existence fact"),
        "reduced-fraction theorem should expose an exist! fact:\n{}",
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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
        let mut runtime = Runtime::new_with_builtin_code();
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
                let mut runtime = Runtime::new_with_builtin_code();
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
        let mut runtime = Runtime::new_with_builtin_code();
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
