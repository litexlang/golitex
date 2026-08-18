use super::*;

#[test]
fn requested_numeric_builtin_rules_verify_with_explicit_provenance() {
    run_with_large_stack(
        "requested_numeric_builtin_rules_verify_with_explicit_provenance",
        || {
            let source_code = r#"
forall a, b R:
    =>:
        a = 0 and b = 0
    <=>:
        a ^ 2 + b ^ 2 = 0

forall a, b R:
    a * b != 0
    =>:
        a != 0 and b != 0

forall a R+, b R*:
    a = (a ^ b) ^ (1 / b)
    a = (a ^ (1 / b)) ^ b

forall n Z, k N+:
    (-n) % k = (k - (n % k)) % k

forall n Z, m Z:
    n >= m or n <= m - 1

forall n Z, m N+, k N+:
    n ^ m % k = ((n % k) ^ m) % k

forall n N+:
    2 ^ (n - 1) != 0
    2 ^ (n - 1 + 1) = 2 ^ (n - 1) * 2 ^ 1
    0 ^ (1 / n) = 0

forall x R:
    -abs(x) <= x

forall S finite_set:
    finite_set_size(S) = 0
    =>:
        S = {}

forall S finite_set:
    finite_set_size(S) != 0
    =>:
        finite_set_size(S) >= 1

forall a Z, b Q:
    (a, b)[1] $in Z
    (a, b)[2] $in Q
    (a - 1, b)[1] $in R

forall a fn(a_index Z) R, m, n, k Z:
    m <= n
    =>:
        sum(m, n, fn(left_index Z) R {a(left_index)}) = sum(m + k, n + k, fn(right_index Z) R {a(right_index - k)})

have x, y R
trust x ^ 2 + y ^ 2 = 0
x = 0
y = 0

have p, q R
trust p * q != 0
p != 0
q != 0

have X finite_set
trust finite_set_size(X) >= 1
have f fn(element X) R
have g, h fn(enum_index closed_range(1, finite_set_size(X))) X
trust forall target_element X:
    exist! preimage_index closed_range(1, finite_set_size(X)) st {g(preimage_index) = target_element}
trust forall target_element X:
    exist! preimage_index closed_range(1, finite_set_size(X)) st {h(preimage_index) = target_element}
by thm finite_set_sum_substitution(finite_set_sum(X, f), finite_set_sum(closed_range(1, finite_set_size(X)), fn(enum_index closed_range(1, finite_set_size(X))) R {f(g(enum_index))}))
sum(1, finite_set_size(X), fn(left_index closed_range(1, finite_set_size(X))) R {f(g(left_index))}) = sum(1, finite_set_size(X), fn(right_index closed_range(1, finite_set_size(X))) R {f(h(right_index))})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "requested_numeric_builtin_rules_verify_with_explicit_provenance",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "requested numeric builtin rules should verify directly:\n{run_output}"
            );
            for rule in [
                "equality: a = 0 from a^2 + b^2 = 0 over R",
                "product_nonzero_component: a * b != 0 gives a != 0 and b != 0",
                "equality: (a^m)^n = a^(m*n) for real exponents over positive real bases",
                "equality: (-n) % k = (k - n % k) % k for n in Z and k in N+",
                "or: integer discrete split x >= n or x <= n - 1",
                "equality: n^m % k = ((n % k)^m) % k for n in Z, m in N, and k in N+",
                "local builtin order.neg_abs_le",
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
fn numeric_builtin_rules_consume_complete_disjunction_premises() {
    run_with_large_stack(
        "numeric_builtin_rules_consume_complete_disjunction_premises",
        || {
            let source_code = r#"
forall x, y R:
    x != 0 or y != 0
    =>:
        x^2 + y^2 != 0

forall a, b, c R:
    0 < c
    c * a <= b or a * c <= b
    =>:
        a <= b / c
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "numeric_builtin_rules_consume_complete_disjunction_premises",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "numeric builtin rules should consume known disjunctions as complete premises:\n{run_output}"
            );
            for rule in [
                "square sum not equal zero from nonzero component or",
                "a <= b / c from 0 < c and (c * a <= b or a * c <= b)",
            ] {
                assert!(
                    run_output.contains(rule),
                    "missing compound-premise builtin provenance `{rule}`:\n{run_output}"
                );
            }
        },
    );
}

#[test]
fn requested_numeric_builtin_rules_preserve_their_boundaries() {
    run_with_large_stack(
        "requested_numeric_builtin_rules_preserve_their_boundaries",
        || {
            let cases = [
                (
                    "square_sum_does_not_prove_a_nonzero_component",
                    r#"
have a, b R
trust a ^ 2 + b ^ 2 = 0
a = 1
"#,
                ),
                (
                    "product_nonzero_does_not_prove_a_zero_component",
                    r#"
have a, b R
trust a * b != 0
a = 0
"#,
                ),
                (
                    "power_of_power_requires_reciprocal_exponents",
                    r#"
(2 ^ 2) ^ (1 / 3) = 2
"#,
                ),
                (
                    "integer_mod_negation_does_not_accept_a_wrong_residue",
                    r#"
(-7) % 3 = 1
"#,
                ),
                (
                    "integer_predecessor_split_does_not_apply_to_reals",
                    r#"
forall n, m R:
    n >= m or n <= m - 1
"#,
                ),
                (
                    "strict_real_difference_is_not_discretely_at_least_one",
                    r#"
forall a, b R:
    a < b
    =>:
        b - a >= 1
"#,
                ),
                (
                    "integer_mod_power_does_not_accept_an_extra_residue",
                    r#"
forall n Z, m N+, k N+:
    n ^ m % k = ((n % k) ^ m + 1) % k
"#,
                ),
                (
                    "integer_expression_exponent_does_not_make_zero_base_nonzero",
                    r#"
forall n N+:
    0 ^ (n - 1) != 0
"#,
                ),
                (
                    "absolute_value_lower_bound_does_not_gain_a_strict_offset",
                    r#"
forall x R:
    -abs(x) <= x - 1
"#,
                ),
                (
                    "sum_reindex_requires_the_same_shift_at_both_bounds",
                    r#"
forall a fn(a_index Z) R, m, n, k Z:
    m <= n
    =>:
        sum(m, n, fn(left_index Z) R {a(left_index)}) = sum(m + k, n + k + 1, fn(right_index Z) R {a(right_index - k)})
"#,
                ),
                (
                    "enumeration_sum_requires_both_unique_preimage_facts",
                    r#"
have X finite_set
trust finite_set_size(X) >= 1
have f fn(element X) R
have g, h fn(enum_index closed_range(1, finite_set_size(X))) X
trust forall target_element X:
    exist! preimage_index closed_range(1, finite_set_size(X)) st {g(preimage_index) = target_element}
sum(1, finite_set_size(X), fn(left_index closed_range(1, finite_set_size(X))) R {f(g(left_index))}) = sum(1, finite_set_size(X), fn(right_index closed_range(1, finite_set_size(X))) R {f(h(right_index))})
"#,
                ),
                (
                    "finite_set_sum_substitution_requires_unique_coverage",
                    r#"
have X finite_set
trust finite_set_size(X) >= 1
have f fn(element X) R
have g fn(enum_index closed_range(1, finite_set_size(X))) X
by thm finite_set_sum_substitution(finite_set_sum(X, f), finite_set_sum(closed_range(1, finite_set_size(X)), fn(enum_index closed_range(1, finite_set_size(X))) R {f(g(enum_index))}))
"#,
                ),
                (
                    "finite_set_is_not_empty_without_zero_cardinality",
                    r#"
have empty_candidate finite_set
empty_candidate = {}
"#,
                ),
                (
                    "literal_tuple_projection_does_not_invent_a_narrower_carrier",
                    r#"
forall a R, b C:
    (a, b)[2] $in R
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
                    !run_succeeded,
                    "{name} must remain outside the builtin rule boundary:\n{run_output}"
                );
            }
        },
    );
}
