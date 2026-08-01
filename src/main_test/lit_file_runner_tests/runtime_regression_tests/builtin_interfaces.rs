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
by thm fn_set_member(fn(x R) R {x}, fn(y R) R)
by thm set_builder_member(1, {x R: x > 0})

have fn circle(r R_pos) power_set(cart(R, R)) = {x cart(R, R): x[1] ^ 2 + x[2] ^ 2 = r ^ 2}
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
        assert!(output.contains("\"theorem_source\": \"builtin_rule\""));
        assert!(output.contains("\"requirement_checks\":"));
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
    ];

    for (label, source, expected) in cases {
        let (_, succeeded, output) = run_source(source, label, false);
        assert!(!succeeded, "{label} should fail:\n{output}");
        assert!(output.contains(expected), "{label}:\n{output}");
    }
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
fn positive_builtin_definitions_require_explicit_by_def() {
    let definition = r#"
prop positive(x R):
    x > 0
$positive(1)
"#;
    let (_, succeeded, output) = run_source(definition, "implicit_definition_disabled", false);
    assert!(
        !succeeded,
        "a positive prop must not fold implicitly:\n{output}"
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
fn builtin_recursive_goal_budget_is_enforced_on_real_power_set_proofs() {
    run_with_large_stack("builtin_recursive_power_set_budget", || {
        let at_limit = format!("$is_finite_set({})", nested_call("power_set", "{1}", 64));
        let (_, succeeded, output) = run_source(&at_limit, "power_set_depth_64", false);
        assert!(
            succeeded,
            "the sixty-fourth recursive builtin child should be allowed:\n{output}"
        );

        let over_limit = format!("$is_finite_set({})", nested_call("power_set", "{1}", 65));
        let (_, succeeded, output) = run_source(&over_limit, "power_set_depth_65", false);
        assert!(
            !succeeded,
            "the sixty-fifth recursive builtin child should return Unknown:\n{output}"
        );
    });
}

#[test]
fn deeply_nested_sqrt_stays_within_the_builtin_recursion_budget() {
    run_with_large_stack("deeply_nested_sqrt_builtin", || {
        let nested_sqrt = nested_call("sqrt", "x", 24);
        let source = format!("have x R\ntrust x >= 0\n{nested_sqrt} >= 0");
        let (_, succeeded, output) = run_source(&source, "deeply_nested_sqrt_builtin", false);
        assert!(
            succeeded,
            "nested square-root nonnegativity should stay automatic below the budget:\n{output}"
        );
    });
}
