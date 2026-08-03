use super::*;

#[test]
fn finite_sum_pointwise_congruence_uses_a_range_guarded_forall() {
    let source_code = r#"
have f fn(f_index Z) Z
have g fn(g_index Z) Z

axiom f_g_agree_on_range:
    ? forall point_index Z:
        1 <= point_index
        point_index <= 3
        =>:
            f(point_index) = g(point_index)

sum(1, 3, fn(left_index Z) Z {f(left_index)}) = sum(1, 3, fn(right_index Z) Z {g(right_index)})

have positive_f fn(positive_f_index N+) Z
have positive_g fn(positive_g_index N+) Z
have lower_bound N+
axiom lower_bound_le_three:
    ? forall:
        lower_bound <= 3
axiom positive_f_g_agree_on_range:
    ? forall positive_index N+:
        lower_bound <= positive_index
        positive_index <= 3
        =>:
            positive_f(positive_index) = positive_g(positive_index)
sum(lower_bound, 3, fn(positive_left_index N+) Z {positive_f(positive_left_index)}) = sum(lower_bound, 3, fn(positive_right_index N+) Z {positive_g(positive_right_index)})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_sum_pointwise_congruence_uses_a_range_guarded_forall",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "range-guarded pointwise equality should imply equality of finite sums:\n{run_output}"
    );
    assert!(
        run_output.contains(
            "equality: finite sums are congruent from pointwise equality on the shared integer range"
        ),
        "the result should expose the finite-sum congruence rule:\n{run_output}"
    );
}

#[test]
fn finite_sum_shift_reindex_uses_a_range_guarded_forall() {
    let source_code = r#"
have f fn(f_index Z) Z
have g fn(g_index Z) Z

axiom shifted_terms_agree_on_range:
    ? forall target_index Z:
        0 <= target_index
        target_index <= 2
        =>:
            f((target_index + 1) - 1) = g(target_index)

sum(1, 3, fn(source_index Z) Z {f(source_index - 1)}) = sum(0, 2, fn(target_index Z) Z {g(target_index)})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_sum_shift_reindex_uses_a_range_guarded_forall",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "range-guarded pointwise equality should justify shifted finite-sum reindexing:\n{run_output}"
    );
    assert!(
        run_output.contains(
            "equality: sum reindexing (integer shift) from pointwise equality on the range"
        ),
        "the result should expose the finite-sum shift rule:\n{run_output}"
    );
}

#[test]
fn real_order_reflexivity_and_strict_irreflexivity_use_number_computation() {
    run_with_large_stack(
        "real_order_reflexivity_and_strict_irreflexivity_use_number_computation",
        || {
            let source_code = r#"
forall a R:
        not a < a
        a <= a
        not a > a
        a >= a
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "real_order_reflexivity_and_strict_irreflexivity_use_number_computation",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "real-order reflexivity and strict irreflexivity should verify:\n{run_output}"
            );
            assert!(
                run_output.contains("number comparison"),
                "all normalized comparison spellings should use the same computation route:\n{run_output}"
            );
            assert!(
                !run_output.contains("order: strict real order is irreflexive")
                    && !run_output.contains("order: weak real order is reflexive"),
                "comparison spellings must not create separate provenance paths:\n{run_output}"
            );
        },
    );
}

#[test]
fn infinite_set_minus_rule_keeps_a_finite_deletion_infinite() {
    let source_code = r#"
forall X set, s finite_set:
    not $is_finite_set(X)
    =>:
        not $is_finite_set(set_minus(X, s))

forall X set, a N:
    not $is_finite_set(X)
    =>:
        not $is_finite_set(set_minus(X, closed_range(0, a)))
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "infinite_set_minus_rule_keeps_a_finite_deletion_infinite",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite deletion from an infinite set should stay infinite:\n{run_output}"
    );
    assert!(
        run_output
            .contains("set minus is infinite when left side is infinite and right side is finite"),
        "the result should expose the finite-deletion rule:\n{run_output}"
    );
}

#[test]
fn infinite_set_minus_rule_requires_both_finiteness_premises() {
    for (name, source_code) in [
        (
            "missing_left_infinite_premise",
            r#"
forall X set, s finite_set:
    not $is_finite_set(set_minus(X, s))
"#,
        ),
        (
            "missing_right_finite_premise",
            r#"
forall X, s set:
    not $is_finite_set(X)
    =>:
        not $is_finite_set(set_minus(X, s))
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
            "{name} must not prove the infinite set-minus conclusion:\n{run_output}"
        );
    }
}

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

forall k N+:
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
fn euclidean_remainder_accepts_a_known_natural_quotient_as_an_integer_leaf() {
    let source_code = r#"
have a N
have d Z
trust d = 3 * a
d = 3 * a + 0
d % 3 = 0
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "euclidean_remainder_accepts_a_known_natural_quotient_as_an_integer_leaf",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "Euclidean remainder uniqueness should accept N as a static subset of Z:\n{run_output}"
    );
    assert!(run_output
        .contains("equality: Euclidean remainder uniqueness from a = m * q + r and 0 <= r < m"));
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
    a <= finite_set_max(union({a}, {b}))
    b <= finite_set_max(union({a}, {b}))
    finite_set_min(union({a}, {b})) <= a
    finite_set_min(union({a}, {b})) <= b

forall a, b, c R:
    a <= c
    b <= c
    =>:
        finite_set_max(union({a}, {b})) <= c

forall a, b, c R:
    c <= a
    c <= b
    =>:
        c <= finite_set_min(union({a}, {b}))

have n1 R = 1
have n2 R = 2
have selected_max R = finite_set_max({n1, n2})
selected_max >= n1
selected_max >= n2

have selected_min R = finite_set_min({n1, n2})
selected_min <= n1
selected_min <= n2

forall a, b Z:
    a < b
    =>:
        a + 1 <= b
        a <= b - 1
        b - a >= 1

forall s finite_set, t N:
    t < finite_set_size(s)
    =>:
        t + 1 <= finite_set_size(s)

forall a, b Z:
    a < b + 1
    =>:
        a <= b

forall m, n Z:
    m < n + 1
    =>:
        m <= (n + 1) - 1

forall a, b Z:
    =>:
        a <= b
    <=>:
        a < b + 1

forall x, n Z:
    x <= n or x >= n + 1

forall x, n Z:
    n <= x
    x < n + 1
    =>:
        x = n

forall x, n Z:
    n < x
    x <= n + 1
    =>:
        x = n + 1
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
                "finite_set_max: every member is at most the maximum",
                "finite_set_min: the minimum is at most every member",
                "finite_set_max: every member is at most a known-equal maximum",
                "finite_set_min: a known-equal minimum is at most every member",
                "integer successor: a < b gives a + 1 <= b",
                "integer predecessor: a < b gives a <= b - 1",
                "integer difference: a < b gives b - a >= 1",
                "integer adjacency: a < b + 1 gives a <= b",
                "or: integer discrete split x <= n or x >= n + 1",
                "integer singleton interval: n <= x < n + 1 gives x = n",
                "integer successor singleton interval: n < x <= n + 1 gives x = n + 1",
            ] {
                assert!(
                    run_output.contains(rule),
                    "missing builtin provenance `{}`:\n{}",
                    rule,
                    run_output
                );
            }
            assert!(
                run_output.matches("\"type\": \"builtin strategy\"").count() >= 2,
                "finite-set upper/lower bounds should use the structural strategy route:\n{run_output}"
            );
        },
    );
}

#[test]
fn integer_successor_singleton_interval_requires_both_bounds() {
    for (name, source_code) in [
        (
            "successor_singleton_missing_strict_lower_bound",
            r#"
forall x, n Z:
    x <= n + 1
    =>:
        x = n + 1
"#,
        ),
        (
            "successor_singleton_missing_weak_upper_bound",
            r#"
forall x, n Z:
    n < x
    =>:
        x = n + 1
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
            "{name} must not prove the successor endpoint without both bounds:\n{run_output}"
        );
    }
}

#[test]
fn integer_discrete_split_accepts_a_natural_subject_and_literal_base() {
    run_with_large_stack(
        "integer_discrete_split_accepts_a_natural_subject_and_literal_base",
        || {
            let source_code = r#"
forall n N:
    n <= 1 or n >= 1 + 1
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "integer_discrete_split_accepts_a_natural_subject_and_literal_base",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "integer discreteness should cover natural subjects and literal integer bases:\n{run_output}"
            );
            assert!(
                run_output.contains("or: integer discrete split x <= n or x >= n + 1"),
                "missing integer-discreteness provenance:\n{run_output}"
            );
        },
    );
}

#[test]
fn positive_natural_predecessor_is_natural_in_recursive_definitions() {
    run_with_large_stack(
        "positive_natural_predecessor_is_natural_in_recursive_definitions",
        || {
            let source_code = r#"
forall n N:
    n > 0
    =>:
        n - 1 $in N

have fn predecessor_count(n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: predecessor_count(n - 1)

predecessor_count(0) = 0
predecessor_count(1) = predecessor_count(0) = 0

forall n N+:
    n - 1 $in N

forall n N+:
    n > 1
    =>:
        n - 1 $in N+

forall n N+:
    2 <= n
    =>:
        n - 1 $in N+

have fn positive_predecessor_count(n N+) N+ by induc n from 1:
    case n = 1: 1
    case n > 1: positive_predecessor_count(n - 1)

positive_predecessor_count(1) = 1
positive_predecessor_count(2) = positive_predecessor_count(1) = 1

have fn hanoi_moves_predecessor_probe(n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: 2 * hanoi_moves_predecessor_probe(n - 1) + 1

have fn shifted_hanoi_moves_predecessor_probe(n N) N = hanoi_moves_predecessor_probe(n) + 1

thm shifted_hanoi_recurrence_predecessor_probe:
    ? forall n N+:
        shifted_hanoi_moves_predecessor_probe(n) = 2 * shifted_hanoi_moves_predecessor_probe(n - 1)
    hanoi_moves_predecessor_probe(n) = 2 * hanoi_moves_predecessor_probe(n - 1) + 1
    shifted_hanoi_moves_predecessor_probe(n - 1) = hanoi_moves_predecessor_probe(n - 1) + 1
    shifted_hanoi_moves_predecessor_probe(n) = hanoi_moves_predecessor_probe(n) + 1 = 2 * hanoi_moves_predecessor_probe(n - 1) + 1 + 1 = 2 * (hanoi_moves_predecessor_probe(n - 1) + 1) = 2 * shifted_hanoi_moves_predecessor_probe(n - 1)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "positive_natural_predecessor_is_natural_in_recursive_definitions",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "positive natural predecessor builtin rule failed:\n{run_output}"
            );
            assert!(
                run_output.contains("N: n - 1 from n in N and n > 0"),
                "missing positive natural predecessor provenance:\n{run_output}"
            );
            assert!(
                run_output.contains("N: n - 1 from n in N+"),
                "missing positive-natural-to-natural predecessor provenance:\n{run_output}"
            );
            assert!(
                run_output.contains("N+: n - 1 from n in N+ and n > 1"),
                "missing strictly positive predecessor provenance:\n{run_output}"
            );

            for (name, invalid_source) in [
                (
                    "zero_does_not_have_a_natural_predecessor",
                    "forall n N:\n    n - 1 $in N",
                ),
                (
                    "positive_natural_predecessor_need_not_be_positive",
                    "forall n N:\n    n > 0\n    =>:\n        n - 1 $in N+",
                ),
                (
                    "positive_natural_predecessor_requires_greater_than_one_to_stay_positive",
                    "forall n N+:\n    n - 1 $in N+",
                ),
            ] {
                let mut boundary_runtime = Runtime::new();
                boundary_runtime.new_file_path_new_env_new_name_scope(name);
                let (boundary_results, boundary_error) =
                    run_source_code(invalid_source, &mut boundary_runtime);
                let (boundary_succeeded, boundary_output) = render_run_source_code_output(
                    &boundary_runtime,
                    &boundary_results,
                    &boundary_error,
                    false,
                );
                assert!(
                    !boundary_succeeded,
                    "{name} must stay outside the builtin boundary:\n{boundary_output}"
                );
            }
        },
    );
}

#[test]
fn number_theory_for_beginners_migration_builtin_patterns() {
    run_with_large_stack(
        "number_theory_for_beginners_migration_builtin_patterns",
        || {
            let source_code = r#"
forall z, q Z:
    z - q $in Z

forall gap Z:
    gap > 0
    =>:
        gap $in N+

forall G set, L fn(x G) power_set(G):
    fn_range(L) $subset power_set(G)

forall m N:
    (-1) ^ (2 * m + 1) = -1

forall m Z:
    m < 0
    =>:
        m <= -1

i $in C
re(1) = 1
re(i) = 0
img(1) = 0
img(i) = 1
re(1 + i) = re(1) + re(i)
re(1 + i) = 1
img(1 + i) = img(1) + img(i)
img(1 + i) = 1
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "number_theory_for_beginners_migration_builtin_patterns",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "Number Theory for Beginners migration patterns should verify:\n{run_output}"
            );
            for rule in [
                "N+: 0 < x and x in Z",
                "function range subset codomain",
                "equality: (-1)^(2*m+1) = -1 for m in N",
                "integer adjacency: a < b + 1 gives a <= b",
                "re: coordinate of complex sum or difference",
                "img: coordinate of complex sum or difference",
            ] {
                assert!(
                    run_output.contains(rule),
                    "missing migration builtin provenance `{rule}`:\n{run_output}"
                );
            }
        },
    );
}

#[test]
fn set_minus_membership_excludes_the_removed_set() {
    run_with_large_stack("set_minus_membership_excludes_the_removed_set", || {
        let source_code = r#"
forall A, B set, x set:
    x $in set_minus(A, B)
    =>:
        not x $in B
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("set_minus_membership_excludes_the_removed_set");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert!(
            run_succeeded,
            "set-minus membership should exclude the removed set:\n{run_output}"
        );
        assert!(
            run_output.contains("\"not x $in B\""),
            "missing set-minus elimination consequence:\n{run_output}"
        );
    });
}

#[test]
fn extrema_equalities_do_not_recurse_through_weak_order() {
    run_with_large_stack(
        "extrema_equalities_do_not_recurse_through_weak_order",
        || {
            let source_code = r#"
have u, v R
trust u <= v
finite_set_min(union({u}, {v})) <= u
u <= finite_set_min(union({u}, {v}))
finite_set_min(union({u}, {v})) = u
-v <= -u
finite_set_max(union({-u}, {-v})) <= -u
-u <= finite_set_max(union({-u}, {-v}))
finite_set_max(union({-u}, {-v})) = -u
-finite_set_max(union({-u}, {-v})) = -(-u)

have epsilon R+
have a, b, A, B R
trust abs(a - A) < epsilon
trust abs(b - B) < epsilon
trust a < b
finite_set_max(union({a}, {b})) = b
trust A < B
finite_set_max(union({A}, {B})) = B
abs(finite_set_max(union({a}, {b})) - finite_set_max(union({A}, {B}))) = abs(b - B) < epsilon
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "extrema_equalities_do_not_recurse_through_weak_order",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "extrema equality rewrites must terminate:\n{}",
                run_output
            );
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

forall a N+, n N:
    a^n $in N+

forall n N+:
    0^(1/n) = 0
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
sqrt(2) != 0
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

        let mut invalid_runtime = Runtime::new();
        invalid_runtime
            .new_file_path_new_env_new_name_scope("sqrt_zero_is_not_incorrectly_proved_nonzero");
        let (stmt_results, runtime_error) = run_source_code("sqrt(0) != 0", &mut invalid_runtime);
        let (run_succeeded, _) =
            render_run_source_code_output(&invalid_runtime, &stmt_results, &runtime_error, false);
        assert!(
            !run_succeeded,
            "the sqrt nonzero rule must require a strictly positive argument"
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
        sqrt(b) > 0
        sqrt(b) != 0
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

    let a_key = runtime.declared_identifier_obj("a").to_string();
    let b_key = runtime.declared_identifier_obj("b").to_string();
    let c_key = runtime.declared_identifier_obj("c").to_string();
    let d_key = runtime.declared_identifier_obj("d").to_string();
    let env = &runtime.current_module().main_environment;
    match env.known_obj_values.get(&a_key) {
        Some(KnownObjValue::SimplifiedFraction(div)) => {
            assert_eq!(div.left.to_string(), "1");
            assert_eq!(div.right.to_string(), "6");
        }
        other => panic!(
            "expected a to store SimplifiedFraction(1 / 6), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get(&b_key) {
        Some(KnownObjValue::SimplifiedNumber(number)) => {
            assert_eq!(number.normalized_value, "0.5");
        }
        other => panic!(
            "expected b to store SimplifiedNumber(0.5), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get(&c_key) {
        Some(KnownObjValue::SimplifiedFraction(div)) => {
            assert_eq!(div.left.to_string(), "-1");
            assert_eq!(div.right.to_string(), "3");
        }
        other => panic!(
            "expected c to store SimplifiedFraction(-1 / 3), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get(&d_key) {
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

have e1 R
trust e1 $in '(,1)
e1 $in R
e1 < 1

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
fn symmetric_interval_center_membership_uses_positive_radius() {
    let positive_source = r#"
forall center R, radius R+:
    center $in '(center - radius, center + radius)
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.isolated = true;
    positive_runtime.new_file_path_new_env_new_name_scope(
        "symmetric_interval_center_membership_uses_positive_radius",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "a center should lie in its positive-radius open interval:\n{positive_output}"
    );

    let unrestricted_radius = r#"
forall center, radius R:
    center $in '(center - radius, center + radius)
"#;
    let mut boundary_runtime = Runtime::new();
    boundary_runtime.isolated = true;
    boundary_runtime.new_file_path_new_env_new_name_scope(
        "symmetric_interval_center_membership_rejects_unrestricted_radius",
    );
    let (boundary_results, boundary_error) =
        run_source_code(unrestricted_radius, &mut boundary_runtime);
    let (boundary_succeeded, boundary_output) =
        render_run_source_code_output(&boundary_runtime, &boundary_results, &boundary_error, false);
    assert!(
        !boundary_succeeded,
        "an unrestricted radius must not justify open-interval membership:\n{boundary_output}"
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
fn even_power_order_chain_implies_absolute_value_order() {
    run_with_large_stack(
        "even_power_order_chain_implies_absolute_value_order",
        || {
            let source_code = r#"
forall x, y R:
    x^2 + y^2 <= 4
    =>:
        (x + y)^2 <= (x + y)^2 + (x - y)^2 = 2 * (x^2 + y^2) <= 2 * 4 = 8 <= 9 = 3^2
        (x + y)^2 <= 3^2
        abs(x + y) <= abs(3)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "even_power_order_chain_implies_absolute_value_order",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a stored even-power inequality should compare absolute values:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn absolute_value_upper_bound_accepts_direct_two_sided_sandwich_only() {
    let positive_source = r#"
have x R
have epsilon R+
trust -epsilon < x
trust x < epsilon
abs(x) < epsilon
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.new_file_path_new_env_new_name_scope(
        "absolute_value_upper_bound_accepts_direct_two_sided_sandwich",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "a direct two-sided sandwich should prove the absolute-value bound:\n{positive_output}"
    );

    let negative_source = r#"
have x R
have epsilon R+
trust x < epsilon
abs(x) < epsilon
"#;
    let mut negative_runtime = Runtime::new();
    negative_runtime.new_file_path_new_env_new_name_scope(
        "absolute_value_upper_bound_requires_both_sides_of_sandwich",
    );
    let (negative_results, negative_error) =
        run_source_code(negative_source, &mut negative_runtime);
    let (negative_succeeded, negative_output) =
        render_run_source_code_output(&negative_runtime, &negative_results, &negative_error, false);
    assert!(
        !negative_succeeded,
        "one upper side alone must not prove an absolute-value bound:\n{negative_output}"
    );
}

#[test]
fn real_power_and_order_builtins_require_real_operands() {
    run_with_large_stack(
        "real_power_and_order_builtins_require_real_operands",
        || {
            let positive_source = r#"
have a, b, c, d, e1, f, x R
have n N+
trust:
    0 < a
    0 <= a
    not a <= x
    a < b
    c <= d
    d <= c
    3 <= e1
    e1 < 3
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
2 <= e1
e1 < 4
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
                    "have S set\nhave n N+\ntrust 0 <= S\n0 <= S^n",
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

forall x Q, n N+:
    x^n = 0
    =>:
        x = 0

forall x, y Q, n N+:
    x >= y
    y >= 0
    =>:
        x^n >= y^n
        y^n >= 0

forall x R, n N:
    abs(x^n) = abs(x)^n

forall x Q*, n, m Z:
    x^n * x^m = x^(n + m)

forall x Q*, n, m Z:
    x^n != 0
    =>:
        (x^n)^m = x^(n * m)

forall m N:
    (-1)^(m + 1) = (-1)^m * (-1)^1

forall m Z:
    (-1)^(m + 1) = (-1)^m * (-1)^1

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
        assert!(run_output.contains("equality: x^(1/n) = z from x = z^n, n in N+, and z >= 0"));
    });
}

#[test]
fn positive_real_power_addition_is_builtin() {
    run_with_large_stack("positive_real_power_addition_is_builtin", || {
        let cases = [
            (
                "positive_real_power_addition_forward",
                r#"
forall a R+, b, c R:
    a^(b + c) = a^b * a^c
"#,
            ),
            (
                "positive_real_power_addition_reverse",
                r#"
forall a R+, b, c R:
    a^b * a^c = a^(b + c)
"#,
            ),
            (
                "positive_real_power_addition_rational_exponents",
                r#"
forall x R+, q, r Q:
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
forall a R*, b, c R:
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
forall a R+, b, c R:
    (a^b)^c = a^(b * c)
"#,
            ),
            (
                "positive_real_power_of_power_reverse",
                r#"
forall a R+, b, c R:
    a^(b * c) = (a^b)^c
"#,
            ),
            (
                "positive_real_power_of_power_nth_root",
                r#"
forall x R, n N+:
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

have c, D set
trust:
    $is_nonempty_set(D)

$is_nonempty_set(union(c, D))
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

have x, A, B, c, D, E, F, G, H, U, V set

trust:
    x $in A
    x $in B
    x $in c
    not x $in D
    x $in intersect(E, F)
    x $in set_minus(G, H)
    x $in union(U, V)

x $in union(A, H)
x $in intersect(A, B)
x $in set_minus(c, D)

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

forall A, B, c set:
    union(union(A, B), c) = union(A, union(B, c))

forall A set:
    union(A, A) = A
    union(A, {}) = A
    union({}, A) = A

have A, B, c set
union(A, B) = union(B, A)
union(union(A, B), c) = union(A, union(B, c))
union(A, union(B, c)) = union(union(A, B), c)
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

forall A, B, c set:
    intersect(intersect(A, B), c) = intersect(A, intersect(B, c))

forall A, B, c set:
    intersect(A, union(B, c)) = union(intersect(A, B), intersect(A, c))

forall A, B, c set:
    set_minus(A, union(B, c)) = intersect(set_minus(A, B), set_minus(A, c))

forall A, B, c set:
    set_minus(A, intersect(B, c)) = union(set_minus(A, B), set_minus(A, c))

forall A, B set:
    B $subset A
    =>:
        B = set_minus(A, set_minus(A, B))
        set_minus(A, set_minus(A, B)) = B

have A, B, c set
intersect(A, B) = intersect(B, A)
intersect(intersect(A, B), c) = intersect(A, intersect(B, c))
intersect(A, intersect(B, c)) = intersect(intersect(A, B), c)
intersect(A, union(B, c)) = union(intersect(A, B), intersect(A, c))
union(intersect(A, B), intersect(A, c)) = intersect(A, union(B, c))
set_minus(A, union(B, c)) = intersect(set_minus(A, B), set_minus(A, c))
intersect(set_minus(A, B), set_minus(A, c)) = set_minus(A, union(B, c))
set_minus(A, intersect(B, c)) = union(set_minus(A, B), set_minus(A, c))
union(set_minus(A, B), set_minus(A, c)) = set_minus(A, intersect(B, c))
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
    assert!(
        run_output.contains("set minus recovers subset from relative complement"),
        "the subset recovery equality should report its builtin rule:\n{}",
        run_output
    );
}

#[test]
fn set_minus_subset_recovery_requires_subset() {
    let source_code = r#"
have A, B set
B = set_minus(A, set_minus(A, B))
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("set_minus_subset_recovery_requires_subset");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "subset recovery must require the subset premise:\n{}",
        run_output
    );
    assert!(
        run_output.contains("UnknownError"),
        "the missing subset premise should leave the equality unknown:\n{}",
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
fn euclidean_quotient_unique_existence_is_builtin() {
    run_with_large_stack("euclidean_quotient_unique_existence_is_builtin", || {
        let source_code = r#"
forall a Z, d N+:
    exist! q Z st {a = d * q + a % d}
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("euclidean_quotient_unique_existence_is_builtin");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "Euclidean quotient unique existence should be builtin:\n{}",
            run_output
        );
        assert!(
            run_output
                .contains("exist!: unique Euclidean quotient for an integer and positive divisor"),
            "missing Euclidean quotient unique-existence provenance:\n{}",
            run_output
        );
    });
}

#[test]
fn source_defined_integer_quotient_uses_unique_existence_builtin() {
    run_with_large_stack(
        "source_defined_integer_quotient_uses_unique_existence_builtin",
        || {
            let source_code = r#"
have fn integer_quotient by exist!:
    ? forall a Z, d N+:
        exist! q Z st {a = d * q + a % d}

forall a Z, d N+:
    integer_quotient(a, d) $in Z
    a = d * integer_quotient(a, d) + a % d
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "source_defined_integer_quotient_uses_unique_existence_builtin",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "source-defined Euclidean quotient should verify from exist!:\n{}",
                run_output
            );
            assert!(
                run_output.contains(
                    "exist!: unique Euclidean quotient for an integer and positive divisor"
                ),
                "missing source-defined Euclidean quotient provenance:\n{}",
                run_output
            );
        },
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
    ? forall A, B set, c finite_set:
        A $subset B
        B $subset c
        =>:
            $is_finite_set(A)
    by thm subset_of_finite_set_is_finite(B, c)
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
fn finite_set_extrema_are_builtin_interfaces() {
    let source_code = r#"
finite_set_max({1, 2}) = 2
finite_set_max({1, 2, 3, 4}) = 4
finite_set_min({4, -1, 2}) = -1

thm finite_set_extrema_have_defining_properties:
    ? forall S power_set(R), x S:
        $is_finite_set(S)
        $is_nonempty_set(S)
        =>:
            finite_set_max(S) $in S
            x <= finite_set_max(S)
            finite_set_min(S) $in S
            finite_set_min(S) <= x
"#;
    let mut runtime = Runtime::new();
    runtime.isolated = true;
    runtime.new_file_path_new_env_new_name_scope("finite_set_extrema_builtin_interfaces");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite-set extrema should be direct builtin interfaces:\n{run_output}"
    );
    for rule_name in [
        "finite_set_max: the maximum belongs to its set",
        "finite_set_max: every member is at most the maximum",
        "finite_set_min: the minimum belongs to its set",
        "finite_set_min: the minimum is at most every member",
    ] {
        assert!(
            run_output.contains(rule_name),
            "missing finite-set extrema builtin provenance `{rule_name}`:\n{run_output}"
        );
    }
}

#[test]
fn finite_set_extrema_inherit_positive_natural_carriers_in_one_rule() {
    let positive_source = r#"
forall n1, n2 N+:
    finite_set_max(union({n1}, {n2})) $in N+
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.isolated = true;
    positive_runtime.new_file_path_new_env_new_name_scope(
        "finite_set_extrema_inherit_positive_natural_carriers_in_one_rule",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "a maximum of positive naturals should inherit N+ directly:\n{positive_output}"
    );
    assert!(
        positive_output.contains("finite-set extremum: member of a standard numeric superset"),
        "missing finite-set extremum carrier provenance:\n{positive_output}"
    );

    let nonpositive_boundary = r#"
forall n N:
    finite_set_max({n}) $in N+
"#;
    let mut boundary_runtime = Runtime::new();
    boundary_runtime.isolated = true;
    boundary_runtime.new_file_path_new_env_new_name_scope(
        "finite_set_extrema_do_not_invent_positive_natural_carriers",
    );
    let (boundary_results, boundary_error) =
        run_source_code(nonpositive_boundary, &mut boundary_runtime);
    let (boundary_succeeded, boundary_output) =
        render_run_source_code_output(&boundary_runtime, &boundary_results, &boundary_error, false);
    assert!(
        !boundary_succeeded,
        "a merely natural singleton maximum must not be promoted to N+:\n{boundary_output}"
    );
}

#[test]
fn positive_quotient_strategy_descends_through_a_positive_difference() {
    let positive_source = r#"
forall a, b R:
    a > b
    =>:
        (a - b) / 2 $in R+
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.isolated = true;
    positive_runtime.new_file_path_new_env_new_name_scope(
        "positive_quotient_strategy_descends_through_a_positive_difference",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "a positive difference divided by a positive constant should be positive:\n{positive_output}"
    );

    let negative_denominator = r#"
forall a, b R:
    a > b
    =>:
        (a - b) / (-2) $in R+
"#;
    let mut boundary_runtime = Runtime::new();
    boundary_runtime.isolated = true;
    boundary_runtime.new_file_path_new_env_new_name_scope(
        "positive_quotient_strategy_rejects_a_negative_denominator",
    );
    let (boundary_results, boundary_error) =
        run_source_code(negative_denominator, &mut boundary_runtime);
    let (boundary_succeeded, boundary_output) =
        render_run_source_code_output(&boundary_runtime, &boundary_results, &boundary_error, false);
    assert!(
        !boundary_succeeded,
        "a positive numerator over a negative denominator must not be positive:\n{boundary_output}"
    );
}

#[test]
fn positive_base_power_is_nonzero_during_definition_well_definedness() {
    let positive_source = r#"
prop has_positive_index_reciprocal_square(u fn(n N+) R):
    forall n N+:
        u(n) = 1 / n^2
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.isolated = true;
    positive_runtime.new_file_path_new_env_new_name_scope(
        "positive_base_power_is_nonzero_during_definition_well_definedness",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "a positive-natural base power should be nonzero while defining a reciprocal:\n{positive_output}"
    );

    let natural_boundary = r#"
prop has_natural_index_reciprocal_square(u fn(n N) R):
    forall n N:
        u(n) = 1 / n^2
"#;
    let mut boundary_runtime = Runtime::new();
    boundary_runtime.isolated = true;
    boundary_runtime.new_file_path_new_env_new_name_scope(
        "natural_base_power_may_be_zero_during_definition_well_definedness",
    );
    let (boundary_results, boundary_error) =
        run_source_code(natural_boundary, &mut boundary_runtime);
    let (boundary_succeeded, boundary_output) =
        render_run_source_code_output(&boundary_runtime, &boundary_results, &boundary_error, false);
    assert!(
        !boundary_succeeded,
        "an arbitrary natural base may be zero and must not justify a reciprocal:\n{boundary_output}"
    );
}

#[test]
fn positive_interval_lower_bound_keeps_reciprocal_well_defined() {
    let positive_interval = r#"
prop reciprocal_on_positive_interval(a, b R+):
    forall x '[a, b]:
        1 / x $in R
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime.isolated = true;
    positive_runtime.new_file_path_new_env_new_name_scope(
        "positive_interval_lower_bound_keeps_reciprocal_well_defined",
    );
    let (positive_results, positive_error) =
        run_source_code(positive_interval, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "a value above a positive interval endpoint should be nonzero:\n{positive_output}"
    );

    let interval_crossing_zero = r#"
prop reciprocal_on_arbitrary_interval(a, b R):
    forall x '[a, b]:
        1 / x $in R
"#;
    let mut boundary_runtime = Runtime::new();
    boundary_runtime.isolated = true;
    boundary_runtime.new_file_path_new_env_new_name_scope(
        "arbitrary_interval_lower_bound_does_not_prove_nonzero",
    );
    let (boundary_results, boundary_error) =
        run_source_code(interval_crossing_zero, &mut boundary_runtime);
    let (boundary_succeeded, boundary_output) =
        render_run_source_code_output(&boundary_runtime, &boundary_results, &boundary_error, false);
    assert!(
        !boundary_succeeded,
        "an interval with an unrestricted endpoint may contain zero:\n{boundary_output}"
    );
}

#[test]
fn native_binary_max_and_min_calculate() {
    let source_code = r#"
max(1, 2) = 2
min(1, 2) = 1
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("native_binary_max_and_min_calculate");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "native binary min/max should calculate on numeric literals:\n{run_output}"
    );
    assert!(
        run_output.contains("calculation"),
        "native binary min/max should expose calculation provenance:\n{run_output}"
    );
}

#[test]
fn gcd_accepts_known_non_all_zero_disjunction() {
    let source_code = r#"
forall a, b Z:
    a != 0 or b != 0
    =>:
        gcd(a, b) $in N+
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("gcd_accepts_known_non_all_zero_disjunction");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "gcd should be well-defined from the known non-all-zero disjunction:\n{run_output}"
    );
}

#[test]
fn finite_nonempty_natural_set_has_a_builtin_greatest_member() {
    let source_code = r#"
prop is_greatest_natural_member(S power_set(N), maximum N):
    maximum $in S
    forall n N:
        n $in S
        =>:
            n <= maximum

forall S power_set(N):
    $is_finite_set(S)
    $is_nonempty_set(S)
    =>:
        exist maximum N st {$is_greatest_natural_member(S, maximum)}
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_nonempty_natural_set_has_a_builtin_greatest_member",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a finite nonempty natural set should have a greatest member:\n{run_output}"
    );
    assert!(
        run_output.contains("finite nonempty natural set has a greatest member"),
        "the proof should expose the bounded maximum-existence rule:\n{run_output}"
    );
}

#[test]
fn greatest_natural_member_rule_requires_finite_and_nonempty_premises() {
    for (name, source_code) in [
        (
            "greatest_natural_member_without_finiteness",
            r#"
prop is_greatest_natural_member(S power_set(N), maximum N):
    maximum $in S
    forall n N:
        n $in S
        =>:
            n <= maximum

forall S power_set(N):
    $is_nonempty_set(S)
    =>:
        exist maximum N st {$is_greatest_natural_member(S, maximum)}
"#,
        ),
        (
            "greatest_natural_member_without_nonemptiness",
            r#"
prop is_greatest_natural_member(S power_set(N), maximum N):
    maximum $in S
    forall n N:
        n $in S
        =>:
            n <= maximum

forall S power_set(N):
    $is_finite_set(S)
    =>:
        exist maximum N st {$is_greatest_natural_member(S, maximum)}
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
            "the greatest-member rule must reject a missing boundary premise ({name}):\n{run_output}"
        );
    }
}

#[test]
fn integer_ranges_inherit_natural_carriers_from_their_lower_endpoint() {
    let source_code = r#"
forall upper N:
    closed_range(0, upper) $subset N
    range(0, upper) $subset N

forall upper N+:
    closed_range(1, upper) $subset N+
    range(1, upper) $subset N+
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "integer_ranges_inherit_natural_carriers_from_their_lower_endpoint",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "integer ranges with natural lower endpoints should preserve that carrier:\n{run_output}"
    );
    assert!(
        run_output.contains("integer range is contained in its standard numeric carrier"),
        "the proof should expose the integer-range carrier rule:\n{run_output}"
    );
}

#[test]
fn integer_range_natural_carrier_rule_rejects_a_negative_lower_endpoint() {
    let source_code = r#"
closed_range(-2, 2) $subset N
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "integer_range_natural_carrier_rule_rejects_a_negative_lower_endpoint",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "a negative lower endpoint must not imply a natural carrier:\n{run_output}"
    );
}

#[test]
fn negation_maps_known_positive_scalars_to_negative_carriers() {
    let source_code = r#"
forall n N+:
    -n $in Z-

forall q Q+:
    -q $in Q-

forall r R+:
    -r $in R-
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "negation_maps_known_positive_scalars_to_negative_carriers",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "negation of positive scalars should preserve the matching negative carrier:\n{run_output}"
    );
    assert!(
        run_output.contains("negation maps a positive scalar into the matching negative carrier"),
        "negative-carrier provenance is missing:\n{run_output}"
    );
}

#[test]
fn negation_does_not_make_a_merely_nonnegative_integer_strictly_negative() {
    let source_code = r#"
forall n N:
    -n $in Z-
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "negation_does_not_make_a_merely_nonnegative_integer_strictly_negative",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "negation of a possibly-zero natural must not imply Z-:\n{run_output}"
    );
}

#[test]
fn absolute_value_of_a_known_nonzero_integer_is_positive_natural() {
    let source_code = r#"
forall z Z*:
    abs(z) $in N+

forall z Z-:
    abs(z) $in N+
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "absolute_value_of_a_known_nonzero_integer_is_positive_natural",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "absolute value should map nonzero integers to N+:\n{run_output}"
    );
    assert!(
        run_output.contains("absolute value of a known nonzero integer is a positive natural"),
        "absolute-value carrier provenance is missing:\n{run_output}"
    );
}

#[test]
fn absolute_value_of_a_merely_natural_number_need_not_be_positive() {
    let source_code = r#"
forall n N:
    abs(n) $in N+
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "absolute_value_of_a_merely_natural_number_need_not_be_positive",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "abs(0) prevents promotion from N to N+:\n{run_output}"
    );
}

#[test]
fn strict_sign_refines_known_integer_carriers() {
    let source_code = r#"
forall z Z*:
    z > 0
    =>:
        z $in N+

forall z Z*:
    z < 0
    =>:
        z $in Z-
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("strict_sign_refines_known_integer_carriers");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "strict sign should refine a known integer carrier:\n{run_output}"
    );
    assert!(
        run_output
            .contains("refined integer carrier from known integer membership and strict sign"),
        "refined integer-carrier provenance is missing:\n{run_output}"
    );
}

#[test]
fn integer_membership_without_a_strict_sign_does_not_imply_n_pos() {
    let source_code = r#"
forall z Z:
    z $in N+
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "integer_membership_without_a_strict_sign_does_not_imply_n_pos",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "integer membership alone must not imply N+:\n{run_output}"
    );
}

#[test]
fn literal_cart_subsets_are_componentwise() {
    let source_code = r#"
forall A1, A2, B1, B2 set:
    A1 $subset B1
    A2 $subset B2
    =>:
        cart(A1, A2) $subset cart(B1, B2)
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("literal_cart_subsets_are_componentwise");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "componentwise cart subset should verify:\n{run_output}"
    );
    assert!(
        run_output.contains("Cartesian-product subset from componentwise subsets"),
        "componentwise cart subset provenance is missing:\n{run_output}"
    );
}

#[test]
fn literal_cart_subset_requires_every_component_subset() {
    let source_code = r#"
forall A1, A2, B1, B2 set:
    A1 $subset B1
    =>:
        cart(A1, A2) $subset cart(B1, B2)
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "literal_cart_subset_requires_every_component_subset",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "cart subset must require every component subset:\n{run_output}"
    );
}

#[test]
fn union_and_literal_finite_set_subset_introduction_use_known_leaves() {
    let source_code = r#"
forall T set, x T:
    {x} $subset T

forall A, B, T set:
    A $subset T
    B $subset T
    =>:
        union(A, B) $subset T
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "union_and_literal_finite_set_subset_introduction_use_known_leaves",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "set-constructor subset introduction should verify:\n{run_output}"
    );
    for rule in [
        "literal finite-set subset from member facts",
        "union subset from both operand subsets",
    ] {
        assert!(
            run_output.contains(rule),
            "set-constructor subset provenance `{rule}` is missing:\n{run_output}"
        );
    }
}

#[test]
fn union_subset_requires_both_operand_subsets() {
    let source_code = r#"
forall A, B, T set:
    A $subset T
    =>:
        union(A, B) $subset T
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("union_subset_requires_both_operand_subsets");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "union subset must require both operand subsets:\n{run_output}"
    );
}

#[test]
fn set_builder_over_a_finite_integer_range_is_finite() {
    let source_code = r#"
forall upper N:
    $is_finite_set({n closed_range(0, upper): n = upper})

claim:
    ? forall upper N:
        $is_nonempty_set({n closed_range(0, upper): n = upper})
    upper $in {n closed_range(0, upper): n = upper}
    witness $is_nonempty_set({n closed_range(0, upper): n = upper}) from upper

have fn selected_natural(upper N) N = finite_set_min({n closed_range(0, upper): n = upper})
"#;
    let mut runtime = Runtime::new();
    runtime
        .new_file_path_new_env_new_name_scope("set_builder_over_a_finite_integer_range_is_finite");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "filtering a finite integer range should stay finite:\n{run_output}"
    );
    assert!(
        run_output.contains("\"type\": \"builtin strategy\""),
        "the proof should expose the structural finiteness route:\n{run_output}"
    );
}
