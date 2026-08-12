use super::*;

fn run_source(source: &str, label: &str, detailed: bool) -> (Runtime, bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    if detailed {
        runtime.set_output_style(OutputStyle::Detailed);
    }
    let (results, error) = run_source_code(source, &mut runtime);
    let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
    (runtime, succeeded, output)
}

#[test]
fn all_explicit_builtin_theorem_interfaces_succeed() {
    run_with_large_stack("all_explicit_builtin_theorem_interfaces", || {
        let source = r#"
have q Q
by thm rational_has_unique_reduced_fraction(q)

by def {1} $subset {1, 2}
by thm subset_of_finite_set_is_finite({1}, {1, 2})
by thm finite_set_has_bijective_index({})

by thm fn_set_member(fn(x R) R {x}, fn(y R) R)
by thm set_builder_member(1, {x R: x > 0})

have fn circle(r R+) power_set(cart(R, R)) = {x cart(R, R): x[1] ^ 2 + x[2] ^ 2 = r ^ 2}
by thm defined_set_member((3, 4), circle(5))

struct Point:
    first R
    second R
by thm struct_member((1, 2), &Point)
by thm cart_member_from_coordinates((1, 2), cart(R, R))

have I set
have S nonempty_set
have g fn(alpha I) S
trust $is_nonempty_set(big_union(S))
have f fn(alpha I) big_union(S)
trust forall alpha I:
    f(alpha) $in g(alpha)
trust forall X S:
    $is_nonempty_set(X)
trust forall alpha I:
    $is_nonempty_set(g(alpha))
by thm general_cart_member(f, general_cart(I, S, g))
by thm general_cart_nonempty_by_choice_from_family(general_cart(I, S, g))
by thm general_cart_nonempty_by_choice_from_pointwise(general_cart(I, S, g))

by thm sum_le_sum_from_pointwise(sum(1, 2, fn(k Z) R {k}), sum(1, 2, fn(k Z) R {k}))
trust forall k {1, 2}:
    k <= k
by thm finite_set_sum_le_from_pointwise(finite_set_sum({1, 2}, fn(k {1, 2}) R {k}), finite_set_sum({1, 2}, fn(k {1, 2}) R {k}))
have fn nonnegative_term(k {1, 2}) R = k
trust forall k {1, 2}:
    0 <= nonnegative_term(k)
by thm finite_set_summand_le_sum(nonnegative_term(1), finite_set_sum({1, 2}, nonnegative_term))
have tuple t for k <= 2, t[k] = k
by thm tuple_equal_from_coordinates(t, (1, 2))

have X finite_set = {1}
have Y finite_set = {1}
have fn value(x X) R = x
have fn index(y Y) X = y
trust $bijective(Y, X, index)
by thm finite_set_sum_substitution(finite_set_sum(X, value), finite_set_sum(Y, fn(y Y) R {value(index(y))}))

have fn literal_value(x {1}) R = x
have fn enum(k closed_range(1, finite_set_size({1}))) {1} = 1
trust finite_set_size({1}) >= 1
trust $bijective(closed_range(1, finite_set_size({1})), {1}, enum)
by thm sum_over_bijective_finite_set_enumerations(sum(1, finite_set_size({1}), fn(k closed_range(1, finite_set_size({1}))) R {literal_value(enum(k))}), sum(1, finite_set_size({1}), fn(k closed_range(1, finite_set_size({1}))) R {literal_value(enum(k))}))
"#;
        let (_, succeeded, output) = run_source(source, "builtin_theorem_interfaces", true);
        assert!(
            succeeded,
            "all builtin theorem interfaces should succeed:\n{output}"
        );
        assert!(output.contains("\"theorem\": \"rational_has_unique_reduced_fraction\""));
        assert!(output.contains("exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}"));
        assert!(output.contains("\"theorem\": \"subset_of_finite_set_is_finite\""));
        assert!(output.contains("\"theorem\": \"finite_set_has_bijective_index\""));
        assert!(output.contains(
            "exist idx finite_seq({}, finite_set_size({})) st {$bijective(closed_range(1, finite_set_size({})), {}, idx)}"
        ));
        assert!(output.contains("\"theorem_source\": \"builtin_rule\""));
        assert!(output.contains("\"requirement_checks\":"));
        assert!(output.contains("\"role\": \"function signature matches the target function set\""));
        assert!(!output.contains("\"role\": \"requirement\""));
        assert!(!output
            .contains("\"statement\": \"function signature matches the target function set\""));
        assert!(output.contains("\"provenance\": \"axiom_of_choice\""));
    });
}

#[test]
fn builtin_theorem_rejects_arity_shape_and_qualified_names() {
    let cases = [
        (
            "arity",
            "by thm fn_set_member(1)",
            "expects 2 argument(s), but got 1",
        ),
        (
            "shape",
            "by thm set_builder_member(1, R)",
            "invalid target shape",
        ),
        (
            "qualified",
            "by thm M::fn_set_member(fn(x R) R {x}, fn(y R) R)",
            "cannot use keyword as name: fn_set_member",
        ),
        (
            "rational arity",
            "have q Q\nby thm rational_has_unique_reduced_fraction(q, q)",
            "expects 1 argument(s), but got 2",
        ),
        (
            "qualified rational",
            "have q Q\nby thm M::rational_has_unique_reduced_fraction(q)",
            "cannot use keyword as name: rational_has_unique_reduced_fraction",
        ),
        (
            "finite subset arity",
            "by thm subset_of_finite_set_is_finite({1})",
            "expects 2 argument(s), but got 1",
        ),
        (
            "finite index arity",
            "by thm finite_set_has_bijective_index({}, {})",
            "expects 1 argument(s), but got 2",
        ),
        (
            "qualified finite subset",
            "by thm M::subset_of_finite_set_is_finite({1}, {1})",
            "cannot use keyword as name: subset_of_finite_set_is_finite",
        ),
        (
            "qualified finite index",
            "by thm M::finite_set_has_bijective_index({})",
            "cannot use keyword as name: finite_set_has_bijective_index",
        ),
    ];

    for (label, source, expected) in cases {
        let (_, succeeded, output) = run_source(source, label, false);
        assert!(!succeeded, "{label} should fail:\n{output}");
        assert!(output.contains(expected), "{label}:\n{output}");
    }
}

#[test]
fn rational_reduced_fraction_requires_the_explicit_theorem_interface() {
    let direct = r#"
have q Q
exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}
"#;
    let (_, succeeded, output) = run_source(direct, "rational_reduced_fraction_direct", false);
    assert!(
        !succeeded,
        "the reduced-fraction fact must not be proved implicitly:\n{output}"
    );
    assert!(!output.contains("unique rational reduced fraction with positive denominator"));

    let explicit = "have q Q\nby thm rational_has_unique_reduced_fraction(q)";
    let (_, succeeded, output) = run_source(explicit, "rational_reduced_fraction_theorem", false);
    assert!(succeeded, "the explicit theorem should succeed:\n{output}");
    assert!(output.contains("\"theorem\": \"rational_has_unique_reduced_fraction\""));
}

#[test]
fn rational_reduced_fraction_builtin_theorem_requires_a_rational_argument_and_does_not_leak() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("rational_reduced_fraction_no_leak");
    let (setup_results, setup_error) = run_source_code("have x R", &mut runtime);
    let (setup_succeeded, setup_output) =
        render_run_source_code_output(&runtime, &setup_results, &setup_error, false);
    assert!(setup_succeeded, "setup should succeed:\n{setup_output}");

    let call = "by thm rational_has_unique_reduced_fraction(x)";
    let (results, error) = run_source_code(call, &mut runtime);
    let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
    assert!(!succeeded, "a merely real argument must fail:\n{output}");
    assert!(output.contains("requires its argument to belong to `Q`"));

    let target = "exist! p Z, d N+ st {x = p / d, gcd(p, d) = 1}";
    assert!(!runtime.cache_known_facts_contains(target).0);
    let (probe_results, probe_error) = run_source_code(target, &mut runtime);
    let (probe_succeeded, probe_output) =
        render_run_source_code_output(&runtime, &probe_results, &probe_error, false);
    assert!(
        !probe_succeeded,
        "a failed builtin theorem must not store its existential conclusion:\n{probe_output}"
    );
}

#[test]
fn finite_set_builtin_theorems_check_requirements_and_do_not_leak() {
    let mut subset_runtime = Runtime::new();
    subset_runtime.new_file_path_new_env_new_name_scope("finite_subset_builtin_no_leak");
    let (setup_results, setup_error) =
        run_source_code("have A set\nhave B finite_set = {1}", &mut subset_runtime);
    let (setup_succeeded, setup_output) =
        render_run_source_code_output(&subset_runtime, &setup_results, &setup_error, false);
    assert!(
        setup_succeeded,
        "subset setup should succeed:\n{setup_output}"
    );

    let (results, error) = run_source_code(
        "by thm subset_of_finite_set_is_finite(A, B)",
        &mut subset_runtime,
    );
    let (succeeded, output) =
        render_run_source_code_output(&subset_runtime, &results, &error, false);
    assert!(
        !succeeded,
        "the missing subset premise must fail:\n{output}"
    );
    assert!(output.contains("requires that the first argument is a subset of the second"));
    assert!(
        !subset_runtime
            .cache_known_facts_contains("$is_finite_set(A)")
            .0
    );
    let (probe_results, probe_error) = run_source_code("$is_finite_set(A)", &mut subset_runtime);
    let (probe_succeeded, probe_output) =
        render_run_source_code_output(&subset_runtime, &probe_results, &probe_error, false);
    assert!(
        !probe_succeeded,
        "a failed subset theorem must not store its conclusion:\n{probe_output}"
    );

    let mut index_runtime = Runtime::new();
    index_runtime.new_file_path_new_env_new_name_scope("finite_index_builtin_no_leak");
    let (setup_results, setup_error) = run_source_code("have S set", &mut index_runtime);
    let (setup_succeeded, setup_output) =
        render_run_source_code_output(&index_runtime, &setup_results, &setup_error, false);
    assert!(
        setup_succeeded,
        "index setup should succeed:\n{setup_output}"
    );

    let (results, error) = run_source_code(
        "by thm finite_set_has_bijective_index(S)",
        &mut index_runtime,
    );
    let (succeeded, output) =
        render_run_source_code_output(&index_runtime, &results, &error, false);
    assert!(
        !succeeded,
        "a merely set-valued argument must fail:\n{output}"
    );
    assert!(output.contains("requires a finite-set argument"));
    let target = "exist idx finite_seq(S, finite_set_size(S)) st {$bijective(closed_range(1, finite_set_size(S)), S, idx)}";
    assert!(!index_runtime.cache_known_facts_contains(target).0);
}

#[test]
fn failed_builtin_theorem_call_does_not_leak_its_conclusion() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("builtin_theorem_no_leak");
    let target = "0 $in {x R: x = 1}";
    let failed_call = format!("by thm set_builder_member(0, {{x R: x = 1}})");
    let (results, error) = run_source_code(&failed_call, &mut runtime);
    let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
    assert!(
        !succeeded,
        "the missing predicate premise should fail:\n{output}"
    );
    assert!(!runtime.cache_known_facts_contains(target).0);

    let (probe_results, probe_error) = run_source_code(target, &mut runtime);
    let (probe_succeeded, probe_output) =
        render_run_source_code_output(&runtime, &probe_results, &probe_error, false);
    assert!(
        !probe_succeeded,
        "a failed builtin theorem call must not store its conclusion:\n{probe_output}"
    );
}

#[test]
fn builtin_theorem_names_are_reserved_and_normal_theorems_still_fall_back() {
    for (label, source) in [
        ("object", "have fn_set_member R"),
        ("parameter", "forall fn_set_member R:\n    1 = 1"),
        (
            "theorem",
            "thm fn_set_member:\n    ? forall:\n        1 = 1\n    1 = 1",
        ),
        (
            "axiom",
            "axiom fn_set_member:\n    ? forall:\n        1 = 1",
        ),
    ] {
        let (_, succeeded, output) = run_source(source, label, false);
        assert!(!succeeded, "reserved {label} name should fail:\n{output}");
    }

    let (_, succeeded, output) = run_source(
        "have rational_has_unique_reduced_fraction R",
        "reserved_rational_theorem_name",
        false,
    );
    assert!(
        !succeeded,
        "the rational builtin theorem name should be reserved:\n{output}"
    );

    for name in [
        "subset_of_finite_set_is_finite",
        "finite_set_has_bijective_index",
    ] {
        let source = format!("have {name} R");
        let (_, succeeded, output) = run_source(&source, name, false);
        assert!(
            !succeeded,
            "the builtin theorem name `{name}` should be reserved:\n{output}"
        );
    }

    let ordinary = r#"
thm local_reflexivity:
    ? forall x R:
        x = x
    x = x
by thm local_reflexivity(1)
"#;
    let (_, succeeded, output) = run_source(ordinary, "normal_theorem_fallback", true);
    assert!(
        succeeded,
        "ordinary theorem fallback should remain intact:\n{output}"
    );
    assert!(output.contains("\"theorem_source\": \"litex\""));
}

#[test]
fn positive_concrete_definitions_fold_implicitly_and_by_def_rechecks() {
    let definition = r#"
prop positive(x R):
    x > 0
$positive(1)
"#;
    let (_, succeeded, output) = run_source(definition, "implicit_definition_enabled", false);
    assert!(
        succeeded,
        "a positive concrete prop should fold from all checked clauses:\n{output}"
    );
    assert!(output.contains("cite prop def"));

    let missing_clause = r#"
prop positive_and_large(x R):
    x > 0
    x > 2
$positive_and_large(1)
"#;
    let (_, succeeded, output) = run_source(
        missing_clause,
        "implicit_definition_keeps_all_clauses",
        false,
    );
    assert!(
        !succeeded,
        "implicit concrete-prop folding must verify every clause:\n{output}"
    );

    let explicit = r#"
prop positive(x R):
    x > 0
by def $positive(1)
$positive(1)
"#;
    let (_, succeeded, output) = run_source(explicit, "explicit_definition_enabled", false);
    assert!(
        succeeded,
        "the explicit by-def path should succeed:\n{output}"
    );
}

fn nested_call(name: &str, leaf: &str, depth: usize) -> String {
    let mut value = leaf.to_string();
    for _ in 0..depth {
        value = format!("{name}({value})");
    }
    value
}

#[test]
fn finite_set_strategy_is_structural_and_has_no_legacy_node_budget() {
    run_with_large_stack("structural_power_set_strategy", || {
        let deeply_nested = format!("$is_finite_set({})", nested_call("power_set", "{1}", 96));
        let (_, succeeded, output) = run_source(&deeply_nested, "power_set_depth_96", true);
        assert!(
            succeeded,
            "strictly smaller finite-set strategy goals should keep descending structurally:\n{output}"
        );
        assert!(output.contains("\"type\": \"builtin strategy\""));
    });
}

#[test]
fn numeric_order_strategy_preserves_order_under_a_shared_subtraction() {
    let source = r#"
forall a, b, c R:
    a <= b
    =>:
        a - c <= b - c

forall a, b, c R:
    a < b
    =>:
        a - c < b - c

forall x R:
    x + 3 <= 2
    =>:
        9 - 2 * (x + 3) >= 9 - 2 * 2

forall r, s Q:
    s + 3 >= r
    s + r <= 3
    =>:
        ((s + r + r) - s) / 2 <= ((3 + (s + 3)) - s) / 2

forall n N:
    n >= 1 + 1
    =>:
        n^2 >= 2^2

forall n Z:
    n^2 >= 25
    n - 4 >= 1
    =>:
        n^2 * (n - 4) >= 25 * 1
"#;
    let (_, succeeded, output) = run_source(source, "shared_subtraction_order", true);
    assert!(
        succeeded,
        "shared subtraction should be a structural order strategy:\n{output}"
    );
    assert!(output.contains("\"type\": \"builtin strategy\""));
}

#[test]
fn absolute_value_order_strategy_uses_square_comparison() {
    let source = r#"
forall x, y R:
    (x + y)^2 <= 3^2
    =>:
        abs(x + y) <= abs(3)

forall x, y R:
    (x - y)^2 < 4^2
    =>:
        abs(x - y) < abs(4)
"#;
    let (_, succeeded, output) = run_source(source, "absolute_value_square_order", true);
    assert!(
        succeeded,
        "absolute-value order should structurally reduce to real carriers and square order:\n{output}"
    );
    assert!(output.contains("\"type\": \"builtin strategy\""));
    assert!(output.contains("numeric-order strategy: structurally smaller order goals"));
}

#[test]
fn integer_interval_membership_strategy_normalizes_case_bounds() {
    let source = r#"
forall n Z:
    n <= 1
    n >= -2 + 1
    =>:
        n $in -1...1
"#;
    let (_, succeeded, output) = run_source(source, "integer_interval_membership", true);
    assert!(
        succeeded,
        "integer interval membership should decompose into carrier and bound leaves:\n{output}"
    );
    assert!(output.contains("\"type\": \"builtin strategy\""));
    assert!(output.contains("set-membership strategy: constructor membership decomposition"));
}

#[test]
fn tuple_cart_membership_composes_with_numeric_carrier_strategy() {
    let source = r#"
forall x, y, z Z:
    (x, y - z * x) $in cart(Z, Z)
"#;
    let (_, succeeded, output) = run_source(source, "tuple_cart_numeric_carrier", true);
    assert!(
        succeeded,
        "tuple/cart membership should delegate arithmetic coordinates to the numeric-carrier strategy:\n{output}"
    );
    assert!(output.contains("set-membership strategy: constructor membership decomposition"));
    assert!(output.contains("numeric-carrier strategy: structural closure in Z"));
}

#[test]
fn direct_sqrt_nonzero_rule_consumes_only_a_strict_positive_premise() {
    let direct = r#"
have t R
trust t > 0
sqrt(t) != 0
"#;
    let (_, succeeded, output) = run_source(direct, "sqrt_direct_nonzero", false);
    assert!(
        succeeded,
        "sqrt(t) != 0 should consume the direct strict premise t > 0:\n{output}"
    );
    assert!(output.contains("sqrt(x) != 0 from x > 0"));

    let weak_premise = r#"
have t R
trust t >= 0
sqrt(t) != 0
"#;
    let (_, succeeded, output) = run_source(weak_premise, "sqrt_weak_nonzero", false);
    assert!(
        !succeeded,
        "nonnegativity alone must not prove a square root nonzero:\n{output}"
    );
}
