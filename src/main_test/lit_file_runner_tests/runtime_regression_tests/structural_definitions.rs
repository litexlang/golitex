use super::*;

#[test]
fn typed_have_admits_literal_dependent_struct_constructor() {
    let source_code = r#"
struct SizedList<X set, n N>:
    length N
    entries fn(k N_pos: k <= n) X
    <=>:
        length = n

template<X nonempty_set, n N, x X>:
    have repeated &SizedList<X, n> = (n, fn(k N_pos: k <= n) X {x})
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "typed_have_admits_literal_dependent_struct_constructor",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "typed tuple returns should check immediate dependent fields and laws:\n{}",
        run_output
    );

    let invalid_source = r#"
struct SizedList<X set, n N>:
    length N
    entries fn(k N_pos: k <= n) X
    <=>:
        length = n

have invalid &SizedList<R, 2> = (3, fn(k N_pos: k <= 2) R {k})
"#;
    let mut invalid_runtime = Runtime::new();
    invalid_runtime.new_file_path_new_env_new_name_scope(
        "typed_have_rejects_struct_constructor_with_false_law",
    );
    let (stmt_results, runtime_error) = run_source_code(invalid_source, &mut invalid_runtime);
    let (run_succeeded, _) =
        render_run_source_code_output(&invalid_runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "typed tuple admission must reject a constructor whose structure law is false"
    );
}

#[test]
fn direct_literal_tuple_membership_checks_dependent_struct_constructor() {
    let source_code = r#"
struct SizedList<X set, n N>:
    length N
    entries fn(k N_pos: k <= n) X
    <=>:
        length = n

(2, fn(k N_pos: k <= 2) R {k}) $in &SizedList<R, 2>
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "direct_literal_tuple_membership_checks_dependent_struct_constructor",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "direct tuple membership should verify dependent fields and laws:\n{}",
        run_output
    );

    let invalid_source = r#"
struct SizedList<X set, n N>:
    length N
    entries fn(k N_pos: k <= n) X
    <=>:
        length = n

(3, fn(k N_pos: k <= 2) R {k}) $in &SizedList<R, 2>
"#;
    let mut invalid_runtime = Runtime::new();
    invalid_runtime.new_file_path_new_env_new_name_scope(
        "direct_literal_tuple_membership_rejects_false_struct_law",
    );
    let (stmt_results, runtime_error) = run_source_code(invalid_source, &mut invalid_runtime);
    let (run_succeeded, _) =
        render_run_source_code_output(&invalid_runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "direct tuple membership must reject a false dependent structure law"
    );
}

#[test]
fn named_struct_field_projects_through_one_checked_tuple_constructor() {
    let source_code = r#"
struct Pair:
    first R
    second R

have pair_value &Pair = (1, 2)
have selected_second R = &Pair{pair_value}.second
selected_second = 2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "named_struct_field_projects_through_one_checked_tuple_constructor",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "one checked tuple constructor should expose its named structure field:\n{}",
        run_output
    );
}

#[test]
fn obtain_from_exist_unique_preserves_uniqueness_for_struct_members() {
    let source_code = r#"
struct BoxedReal:
    value R
    tag R

abstract_prop selected_box(x)

trust exist! x &BoxedReal st {$selected_box(x)}

obtain chosen from exist! x &BoxedReal st {$selected_box(x)}

forall x1, x2 &BoxedReal:
    $selected_box(x1)
    $selected_box(x2)
    =>:
        x1 = x2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "obtain_from_exist_unique_preserves_uniqueness_for_struct_members",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "exist! elimination must retain its uniqueness projection:\n{}",
        run_output
    );
}

#[test]
fn template_instantiation_prefers_angle_brackets() {
    let source_code = r#"
template<s set: s = s>:
    have id_on_set set = s

\id_on_set<R> = R
\id_on_set{R} = R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("template_instantiation_prefers_angle_brackets");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "template_instantiation_prefers_angle_brackets failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("template<"),
        "template definition display should omit the redundant header name:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("template id_on_set"),
        "template definition display should not repeat the body-defined name in the header:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\\id_on_set<R> = R"),
        "template instantiation display should use angle brackets:\n{}",
        run_output
    );
}

#[test]
fn template_header_rejects_redundant_name() {
    let source_code = r#"
template id_on_set<s set>:
    have id_on_set set = s
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("template_header_rejects_redundant_name");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "template header with redundant name should fail, but succeeded:\n{}",
        run_output
    );
    assert!(
        run_output.contains("template definition expects `template<...>:`"),
        "old template header syntax should report the new syntax:\n{}",
        run_output
    );
}

#[test]
fn template_body_is_still_checked_when_declared() {
    let source_code = r#"
template<S set>:
    have broken S = 1
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("template_body_is_still_checked_when_declared");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "an invalid generic template body must fail at declaration time:\n{}",
        run_output
    );
}

#[test]
fn template_application_still_checks_its_header() {
    let cases = [
        ("wrong_arity", r#"\guarded<R> = R"#, "expects"),
        (
            "wrong_parameter_type",
            r#"\guarded<R, 0> = R"#,
            "parameter types",
        ),
        (
            "unsatisfied_domain_fact",
            r#"\guarded<R, 1> = R"#,
            "domain fact",
        ),
    ];

    for (case_name, application, expected_output) in cases {
        let source_code = format!(
            r#"
template<S set, n N_pos: 2 <= n>:
    have guarded set = S

{}
"#,
            application
        );

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(case_name);
        let (stmt_results, runtime_error) = run_source_code(&source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "invalid template application `{}` should fail:\n{}",
            case_name, run_output
        );
        assert!(
            run_output.contains(expected_output),
            "invalid template application `{}` should mention `{}`:\n{}",
            case_name,
            expected_output,
            run_output
        );
    }

    let source_code = r#"
template<S set, n N_pos: 2 <= n>:
    have guarded set = S

\guarded<R, 2> = R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("valid_template_header");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a valid template application should still instantiate:\n{}",
        run_output
    );
}

#[test]
fn preverified_template_set_builder_alias_still_unfolds() {
    let source_code = r#"
abstract_prop marked(x)

template<S set>:
    have Filtered power_set(S) = {x S: $marked(x)}

have x R
trust x $in \Filtered<R>
$marked(x)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("preverified_template_set_builder_alias_unfolds");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a preverified template instance must still register its set-builder alias:\n{}",
        run_output
    );
}

#[test]
fn deterministic_infer_rule_firings_are_cached() {
    let setup = r#"
struct Box<S set>:
    value S
    tag N

prop accepts(S set, b &Box<S>):
    b.value = b.value

have b &Box<R> = (0, 0)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("deterministic_infer_rule_firings_are_cached");
    let (stmt_results, runtime_error) = run_source_code(setup, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "cached infer-rule setup failed:\n{}",
        run_output
    );

    let (stmt_results, runtime_error) = run_source_code("trust $accepts(R, b)", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "the first predicate inference failed:\n{}",
        run_output
    );
    let counts_after_first = {
        let environment = runtime.top_level_env();
        (
            environment.cache_known_fact.len(),
            environment.cache_infer_rule_firing.len(),
        )
    };

    let (stmt_results, runtime_error) = run_source_code("trust $accepts(R, b)", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "the cached predicate inference failed:\n{}",
        run_output
    );
    let counts_after_second = {
        let environment = runtime.top_level_env();
        (
            environment.cache_known_fact.len(),
            environment.cache_infer_rule_firing.len(),
        )
    };

    assert_eq!(
        counts_after_second, counts_after_first,
        "repeating a known predicate fact must not store facts or fire deterministic infer rules again"
    );
}

#[test]
fn named_struct_membership_does_not_materialize_tuple_projection_view() {
    let source_code = r#"
struct Pair<S set>:
    first S
    second S

have p &Pair<R>
p.first $in R
p.second $in R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "named_struct_membership_does_not_materialize_tuple_projection_view",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "named struct fields must remain available without tuple projection inference:\n{}",
        run_output
    );

    let tuple_related_facts = runtime
        .top_level_env()
        .cache_known_fact
        .keys()
        .filter(|fact| fact.contains("p[") || fact.contains("p $in cart("))
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        tuple_related_facts.is_empty(),
        "named struct membership must not materialize tuple projection facts: {:?}",
        tuple_related_facts
    );
}

#[test]
fn struct_tuple_projection_materializes_cart_view_on_demand() {
    let source_code = r#"
struct Pair<S set>:
    first S
    second S

have p &Pair<R>
p[1] $in R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "struct_tuple_projection_materializes_cart_view_on_demand",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "an explicit projection must lazily materialize its struct cart view:\n{}",
        run_output
    );

    assert!(
        runtime
            .top_level_env()
            .cache_known_fact
            .keys()
            .any(|fact| fact.contains("p $in cart(")),
        "using `p[1]` must materialize the cart membership required by the projection"
    );
}

#[test]
fn tuple_struct_membership_still_materializes_tuple_view() {
    let source_code = r#"
struct Pair<S set>:
    first S
    second S

trust (1, 2) $in &Pair<R>
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("tuple_struct_membership_materializes_tuple_view");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "tuple struct membership must still check and expose tuple components:\n{}",
        run_output
    );

    assert!(
        runtime
            .top_level_env()
            .cache_known_fact
            .keys()
            .any(|fact| fact.contains("(1, 2) $in cart(")),
        "tuple struct membership must retain its cart membership view"
    );
}

#[test]
fn cached_membership_can_use_a_later_set_builder_alias() {
    let source_code = r#"
abstract_prop marked(x)
have x R
have A set
trust x $in A
trust A = {y R: $marked(y)}
trust x $in A
$marked(x)
"#;

    let mut runtime = Runtime::new();
    runtime
        .new_file_path_new_env_new_name_scope("cached_membership_can_use_later_set_builder_alias");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a cached membership must be reconsidered after a new alias appears:\n{}",
        run_output
    );
}

#[test]
fn failed_try_discards_infer_rule_firings() {
    let source_code = r#"
try:
    abstract_prop marked(x)
    have x R
    trust x $in {y R: $marked(y)}
    0 = 1
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("failed_try_discards_infer_rule_firings");
    let firings_before = runtime.top_level_env().cache_infer_rule_firing.len();
    let (_, runtime_error) = run_source_code(source_code, &mut runtime);
    assert!(
        runtime_error.is_some(),
        "the deliberately false try body should fail"
    );
    let firings_after = runtime.top_level_env().cache_infer_rule_firing.len();

    assert_eq!(
        firings_after, firings_before,
        "a failed try block must roll back infer-rule firing cache entries"
    );
}

#[test]
fn template_can_use_struct_with_function_valued_fields() {
    run_with_large_stack(
        "template_can_use_struct_with_function_valued_fields",
        || {
            let source_code = r#"
struct Group<s set>:
    inv fn(x s) s
    op fn(x, y s) s
    identity s
    <=>:
        forall x, y, z s:
            op(x, op(y, z)) = op(op(x, y), z)
        forall x s:
            op(identity, x) = x
        forall x s:
            op(x, identity) = x
        forall x s:
            op(x, inv(x)) = identity
        forall x s:
            op(inv(x), x) = identity

template<s set>:
    have group_quotient fn (g &Group<s>) power_set(s)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_can_use_struct_with_function_valued_fields",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "template_can_use_struct_with_function_valued_fields failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn struct_filter_predicate_unfolds_for_default_field_view() {
    run_with_large_stack(
        "struct_filter_predicate_unfolds_for_default_field_view",
        || {
            let source_code = r#"
prop is_group(s nonempty_set, inv fn(x s) s, op fn(x, y s) s, identity s):
    forall x, y, z s:
        op(x, op(y, z)) = op(op(x, y), z)
    forall x s:
        op(identity, x) = x
        op(x, identity) = x
        op(x, inv(x)) = identity
        op(inv(x), x) = identity

struct Group<s nonempty_set>:
    inv fn(x s) s
    op fn(x, y s) s
    identity s
    <=>:
        $is_group(s, inv, op, identity)

claim:
    ? forall s nonempty_set, g &Group<s>, x s:
        g.op(g.inv(x), x) = g.identity
    g.op(g.inv(x), x) = g.identity
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "struct_filter_predicate_unfolds_for_default_field_view",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "struct_filter_predicate_unfolds_for_explicit_field_view failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn default_struct_view_keeps_explicit_struct_view_syntax_available() {
    run_with_large_stack(
        "default_struct_view_keeps_explicit_struct_view_syntax_available",
        || {
            let source_code = r#"
struct Point:
    x R
    y R

struct CoordinatePair:
    first R
    second R

have explicit_point &Point = (3, 4)
&Point{explicit_point}.x = 3

have p &Point = (1, 2)
p.x = 1
p.y = 2
&Point{p}.x = 1
p $in &CoordinatePair
&CoordinatePair{p}.first = 1
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "default_struct_view_keeps_explicit_struct_view_syntax_available",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "default struct views should coexist with explicit and alternate struct views:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"statement\": \"&Point{p}.y = 2\""),
                "`p.y` should lower directly to the existing explicit struct-field AST:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn default_struct_view_replays_from_theorem_goal_into_proof() {
    run_with_large_stack(
        "default_struct_view_replays_from_theorem_goal_into_proof",
        || {
            let source_code = r#"
struct Point:
    x R
    y R

thm point_default_view_is_available_in_proof:
    ? forall p &Point:
        p.x = &Point{p}.x
    p.x = &Point{p}.x
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "default_struct_view_replays_from_theorem_goal_into_proof",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "theorem proof parsing should replay the goal binder's default struct view:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn parameterized_default_struct_view_keeps_dependent_symbol_ids() {
    run_with_large_stack(
        "parameterized_default_struct_view_keeps_dependent_symbol_ids",
        || {
            let source_code = r#"
struct Box<s set>:
    value s
    tag N

thm box_default_view_keeps_its_carrier:
    ? forall s nonempty_set, b &Box<s>:
        b.value = &Box<s>{b}.value
    b.value = &Box<s>{b}.value
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "parameterized_default_struct_view_keeps_dependent_symbol_ids",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a parameterized default view should retain earlier binder identities:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn struct_membership_fact_does_not_enable_default_field_syntax() {
    let source_code = r#"
struct Point:
    x R
    y R

have p cart(R, R) = (1, 2)
p $in &Point
p.x = &Point{p}.x
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "struct_membership_fact_does_not_enable_default_field_syntax",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "a later `p $in &Point` fact must not opt `p` into `p.x` syntax:\n{}",
        run_output
    );
    assert!(
        run_output.contains("default struct view"),
        "missing-default-view syntax should have a focused diagnostic:\n{}",
        run_output
    );
}

#[test]
fn separate_same_name_binders_keep_symbol_specific_default_struct_views() {
    run_with_large_stack(
        "separate_same_name_binders_keep_symbol_specific_default_struct_views",
        || {
            let source_code = r#"
struct Point:
    x R
    y R

struct TaggedInteger:
    code Z
    tag N

thm point_view_for_item:
    ? forall item &Point:
        item.x = &Point{item}.x
    item.x = &Point{item}.x

thm tagged_integer_view_for_item:
    ? forall item &TaggedInteger:
        item.code = &TaggedInteger{item}.code
    item.code = &TaggedInteger{item}.code
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "separate_same_name_binders_keep_symbol_specific_default_struct_views",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "separate `item` binders should replay defaults by SymbolId, not surface name:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn default_struct_view_function_field_remains_callable() {
    run_with_large_stack(
        "default_struct_view_function_field_remains_callable",
        || {
            let source_code = r#"
struct Endomorphism:
    apply fn(x R) R
    anchor R

have endomorphism &Endomorphism = (fn(x R) R {x + 1}, 0)
endomorphism.apply(2) = &Endomorphism{endomorphism}.apply(2)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "default_struct_view_function_field_remains_callable",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a callable default field should parse as the existing explicit callable AST:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn chained_default_struct_views_support_bundled_vector_space_operations() {
    run_with_large_stack(
        "chained_default_struct_views_support_bundled_vector_space_operations",
        || {
            let source_code = r#"
struct ScalarSystem<s nonempty_set>:
    one s
    add fn(x, y s) s
    mul fn(x, y s) s

struct VectorSpace<s, v nonempty_set>:
    scalars &ScalarSystem<s>
    zero v
    add fn(x, y v) v
    smul fn(a s, x v) v
    <=>:
        forall a, b s, x v:
            smul(scalars.mul(a, b), x) = smul(a, smul(b, x))

claim:
    ? forall s, v nonempty_set, space &VectorSpace<s, v>, a, b s, x v:
        space.smul(space.scalars.mul(a, b), x) = space.smul(a, space.smul(b, x))
    space.smul(space.scalars.mul(a, b), x) = space.smul(a, space.smul(b, x))

prop share_scalar_system(s, v, w nonempty_set, Vspace &VectorSpace<s, v>, Wspace &VectorSpace<s, w>):
    Vspace.scalars = Wspace.scalars
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "chained_default_struct_views_support_bundled_vector_space_operations",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a directly declared struct-valued field should supply the next view:\n{}",
                run_output
            );
            assert!(
                run_output
                    .contains("&ScalarSystem<s>{&VectorSpace<s, v>{space}.scalars}.mul(a, b)"),
                "the chained shorthand should lower to nested explicit views:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn chained_field_access_continues_after_an_explicit_struct_view() {
    run_with_large_stack(
        "chained_field_access_continues_after_an_explicit_struct_view",
        || {
            let source_code = r#"
struct Leaf:
    value R
    marker N

struct Node:
    leaf &Leaf
    marker N

have node &Node = ((1, 0), 0)
&Node{node}.leaf.value $in R
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "chained_field_access_continues_after_an_explicit_struct_view",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "an explicit field access should carry its declared result view into the next hop:\n{}",
                run_output
            );
            assert!(
                run_output.contains("&Leaf{&Node{node}.leaf}.value $in R"),
                "the explicit-base chain should use the existing nested field-access AST:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn chained_default_struct_views_support_module_qualified_field_types() {
    run_with_large_stack(
        "chained_default_struct_views_support_module_qualified_field_types",
        || {
            let source_code = r#"
struct ScalarSystem<s nonempty_set>:
    one s
    mul fn(x, y s) s

struct Bundle<s nonempty_set>:
    scalars &Current::ScalarSystem<s>
    marker N

claim:
    ? forall s nonempty_set, bundle &Bundle<s>:
        bundle.scalars.one $in s
    bundle.scalars.one $in s
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "chained_default_struct_views_support_module_qualified_field_types",
            );
            runtime.current_module_mut().module_name = "Current".to_string();
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a module-qualified declared field type should supply the next view:\n{}",
                run_output
            );
            assert!(
                run_output.contains(
                    "&Current::ScalarSystem<s>{&Current::Bundle<s>{bundle}.scalars}.one $in s"
                ),
                "the nested access should preserve the module-qualified struct view:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn chained_field_access_rejects_non_struct_intermediate_fields() {
    run_with_large_stack(
        "chained_field_access_rejects_non_struct_intermediate_fields",
        || {
            let source_code = r#"
struct Point:
    x R
    y R

have point &Point = (1, 2)
point.x.value = 1
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "chained_field_access_rejects_non_struct_intermediate_fields",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "a scalar field must not silently acquire an inferred struct view:\n{}",
                run_output
            );
            assert!(
                run_output.contains("Point.x")
                    && run_output.contains("is not declared with a struct type")
                    && run_output.contains("&Struct{"),
                "a non-struct intermediate field should report the explicit-view fallback:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn chained_field_access_does_not_follow_aliases_or_known_memberships() {
    run_with_large_stack(
        "chained_field_access_does_not_follow_aliases_or_known_memberships",
        || {
            let source_code = r#"
struct Point:
    x R
    y R

have PointView set = &Point

struct Holder:
    point PointView
    marker N

trust have holder &Holder
trust &Holder{holder}.point $in &Point
holder.point.x = 1
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "chained_field_access_does_not_follow_aliases_or_known_memberships",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "an alias and known membership must not choose an implicit intermediate view:\n{}",
                run_output
            );
            assert!(
                run_output.contains("Holder.point")
                    && run_output.contains("is not declared with a struct type"),
                "only a direct struct field declaration should continue the chain:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn chained_field_access_rejects_access_after_a_function_call() {
    run_with_large_stack(
        "chained_field_access_rejects_access_after_a_function_call",
        || {
            let source_code = r#"
struct Endomorphism:
    apply fn(x R) R
    anchor R

have endomorphism &Endomorphism = (fn(x R) R {x + 1}, 0)
endomorphism.apply(1).value = 2
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "chained_field_access_rejects_access_after_a_function_call",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "field access after a function call is intentionally outside the chained-field feature:\n{}",
                run_output
            );
            assert!(
                run_output.contains("field access after this expression form is not supported")
                    && run_output.contains("&Struct{expr}.field"),
                "the unsupported mixed postfix should have a focused diagnostic:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn default_struct_view_is_available_in_set_builder_body() {
    run_with_large_stack(
        "default_struct_view_is_available_in_set_builder_body",
        || {
            let source_code = r#"
struct Point:
    x R
    y R

have right_half_plane set = {p &Point: p.x >= 0}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "default_struct_view_is_available_in_set_builder_body",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a set-builder binding should make its selected struct view available in the body:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_def_packages_an_exact_known_universal_clause_with_bounded_type_checks() {
    let source_code = r#"
prop maps_into(A set, f fn(n N) A, S power_set(A)):
    forall n N:
        f(n) $in S

trust have f fn(n N) R
trust forall index N:
    f(index) $in {0}
by def $maps_into(R, f, {0})
"#;
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "by_def_packages_an_exact_known_universal_clause_with_bounded_type_checks",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "an exact universal definition clause should package directly:\n{run_output}"
    );
}

#[test]
fn by_def_does_not_package_a_missing_universal_clause() {
    let source_code = r#"
prop maps_into(A set, f fn(n N) A, S power_set(A)):
    forall n N:
        f(n) $in S

trust have f fn(n N) R
by def $maps_into(R, f, {0})
"#;
    let mut runtime = Runtime::new();
    runtime
        .new_file_path_new_env_new_name_scope("by_def_does_not_package_a_missing_universal_clause");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "definition folding must not invent a missing universal premise:\n{run_output}"
    );
}

#[test]
fn default_struct_view_is_available_for_struct_fields() {
    run_with_large_stack("default_struct_view_is_available_for_struct_fields", || {
        let source_code = r#"
struct Point:
    x R
    y R

struct PointHolder:
    point &Point
    marker N
    <=>:
        point.x = &Point{point}.x
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "default_struct_view_is_available_for_struct_fields",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "a struct field typed by `&Point` should use that default view in the filter:\n{}",
            run_output
        );
    });
}

#[test]
fn legacy_double_ampersand_struct_binding_is_rejected_with_migration_hint() {
    let source_code = r#"
struct Point:
    x R
    y R

claim:
    ? forall p &&Point:
        p.x = &Point{p}.x
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "legacy_double_ampersand_struct_binding_is_rejected_with_migration_hint",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "legacy `&&Point` binding syntax should be rejected:\n{}",
        run_output
    );
    assert!(
        run_output.contains("`&&Struct` has been removed")
            && run_output.contains("write `&Struct` in a binding type"),
        "legacy syntax should report the direct `&&Point` to `&Point` migration:\n{}",
        run_output
    );
}

#[test]
fn obtain_inherits_default_struct_view() {
    run_with_large_stack("obtain_inherits_default_struct_view", || {
        let source_code = r#"
struct Point:
    x R
    y R

have original &Point = (1, 2)
witness exist p &Point st {p = p} from original
obtain point from exist p &Point st {p = p}
point.x = &Point{point}.x
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("obtain_inherits_default_struct_view");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "an obtained object should inherit its existential struct view:\n{}",
            run_output
        );
    });
}

#[test]
fn obtain_instantiates_parameterized_default_struct_view_by_symbol_id() {
    run_with_large_stack(
        "obtain_instantiates_parameterized_default_struct_view_by_symbol_id",
        || {
            let source_code = r#"
struct Box<s set>:
    value s
    tag N

have real_box &Box<R> = (1, 0)
witness exist s nonempty_set, b &Box<s> st {b = b} from R, real_box
obtain carrier, box from exist s nonempty_set, b &Box<s> st {b = b}
box.value = &Box<carrier>{box}.value
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "obtain_instantiates_parameterized_default_struct_view_by_symbol_id",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "an obtained dependent struct view should substitute the new carrier SymbolId:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn nested_struct_verification_freshens_same_named_field_binders() {
    run_with_large_stack(
        "nested_struct_verification_freshens_same_named_field_binders",
        || {
            let source_code = r#"
struct ScalarSystem<s nonempty_set>:
    zero s
    one s

have real_scalars &ScalarSystem<R> = (0, 1)

struct VectorSpace<s nonempty_set, scalars &ScalarSystem<s>, v nonempty_set>:
    zero v
    smul fn(a s, x v) v
    <=>:
        forall x v:
            smul(&ScalarSystem<s>{scalars}.one, x) = x

prop is_real_vector_space(v nonempty_set, vector_zero v, vector_smul fn(a R, x v) v):
    (vector_zero, vector_smul) $in &VectorSpace<R, real_scalars, v>
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "nested_struct_verification_freshens_same_named_field_binders",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "nested structs may reuse field names because each struct owns its fields:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_proof_uses_the_instantiated_forall_binder_id() {
    run_with_large_stack(
        "template_proof_uses_the_instantiated_forall_binder_id",
        || {
            let source_code = r#"
axiom unique_self:
    ? forall S nonempty_set, x S:
        exist! y S st {y = x}

template<S nonempty_set>:
    have fn selected_self by exist!:
        ? forall x S:
            exist! y S st {y = x}
        by thm unique_self(S, x)

forall S nonempty_set, x S:
    \selected_self<S>(x) = x
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_proof_uses_the_instantiated_forall_binder_id",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a materialized template proof must use the instantiated forall binder:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_recursive_function_materializes_public_computation_equations() {
    run_with_large_stack(
        "template_recursive_function_materializes_public_computation_equations",
        || {
            let source_code = r#"
template<T nonempty_set, combine fn(left, right T) T, identity T>:
    have fn recursive_fold(values fn(index N) T, count N) T by induc count from 0:
        case count = 0: identity
        case count > 0: combine(recursive_fold(values, count - 1), values(count - 1))

forall T nonempty_set, combine fn(left, right T) T, identity T, values fn(index N) T:
    \recursive_fold<T, combine, identity>(values, 0) = identity

forall T nonempty_set, combine fn(left, right T) T, identity T, values fn(index N) T, count N:
    \recursive_fold<T, combine, identity>(values, count + 1) = combine(\recursive_fold<T, combine, identity>(values, (count + 1) - 1), values((count + 1) - 1)) = combine(\recursive_fold<T, combine, identity>(values, count), values(count))
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_recursive_function_materializes_public_computation_equations",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "template recursive functions must expose equations through their public application:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_case_function_materializes_public_computation_equations() {
    run_with_large_stack(
        "template_case_function_materializes_public_computation_equations",
        || {
            let source_code = r#"
template<T nonempty_set, marker, fallback T>:
    have fn choose_marker(value T) T by cases:
        case value = marker: marker
        case value != marker: fallback

forall T nonempty_set, marker, fallback, value T:
    value = marker
    =>:
        \choose_marker<T, marker, fallback>(value) = marker

forall T nonempty_set, marker, fallback, value T:
    value != marker
    =>:
        \choose_marker<T, marker, fallback>(value) = fallback
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_case_function_materializes_public_computation_equations",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "template case functions must expose equations through their public application:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_simple_function_materializes_public_computation_equation() {
    run_with_large_stack(
        "template_simple_function_materializes_public_computation_equation",
        || {
            let source_code = r#"
template<T nonempty_set, combine fn(left, right T) T, marker T>:
    have fn combine_with_marker(value T) T = combine(value, marker)

forall T nonempty_set, combine fn(left, right T) T, marker, value T:
    \combine_with_marker<T, combine, marker>(value) = combine(value, marker)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_simple_function_materializes_public_computation_equation",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "template simple functions must expose equations through their public application:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_choice_materializes_local_exist_elimination_and_witness() {
    run_with_large_stack(
        "template_choice_materializes_local_exist_elimination_and_witness",
        || {
            let source_code = r#"
axiom self_exists:
    ? forall S nonempty_set, x S:
        exist y S st {y = x}

template<S nonempty_set>:
    have fn selected_self_with_local_proof by exist!:
        ? forall x S:
            exist! y S st {y = x}
        by thm self_exists(S, x)
        obtain y from exist candidate S st {candidate = x}
        witness exist candidate S st {candidate = x} from y
        forall y1, y2 S:
            y1 = x
            y2 = x
            =>:
                y1 = y2

forall S nonempty_set, x S:
    \selected_self_with_local_proof<S>(x) = x
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_choice_materializes_local_exist_elimination_and_witness",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a materialized template proof must retain local exist elimination and witness statements:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_choice_materializes_local_equal_object_definition() {
    run_with_large_stack(
        "template_choice_materializes_local_equal_object_definition",
        || {
            let source_code = r#"
template<S nonempty_set>:
    have fn selected_self_with_local_object by exist!:
        ? forall x S:
            exist! y S st {y = x}
        have candidate S = x
        witness exist y S st {y = x} from candidate
        forall y1, y2 S:
            y1 = x
            y2 = x
            =>:
                y1 = y2

template<S nonempty_set>:
    have fn selected_self_again(x S) S = \selected_self_with_local_object<S>(x)

forall S nonempty_set, x S:
    \selected_self_again<S>(x) $in S
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_choice_materializes_local_equal_object_definition",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a materialized template choice proof must retain local equal-object definitions:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn template_choice_materializes_local_case_function() {
    run_with_large_stack("template_choice_materializes_local_case_function", || {
        let source_code = r#"
template<S nonempty_set, marker S>:
    have fn selected_marker_with_local_case by exist!:
        ? forall x S:
            exist! y S st {y = marker}
        have fn local_marker(input S) S by cases:
            case input = marker: marker
            case input != marker: marker
        witness exist y S st {y = marker} from marker
        forall y1, y2 S:
            y1 = marker
            y2 = marker
            =>:
                y1 = y2

forall S nonempty_set, marker, x S:
    \selected_marker_with_local_case<S, marker>(x) = marker
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "template_choice_materializes_local_case_function",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "a materialized template proof must retain local case-defined functions:\n{}",
            run_output
        );
    });
}

#[test]
fn template_choice_returning_refined_function_remains_callable() {
    run_with_large_stack(
        "template_choice_returning_refined_function_remains_callable",
        || {
            let source_code = r#"
prop is_constant(S nonempty_set, marker S, value fn(x S) S):
    forall x S:
        value(x) = marker

template<S nonempty_set, marker S>:
    have ConstantFunctions power_set(fn(x S) S) = {value fn(x S) S: $is_constant(S, marker, value)}

template<S nonempty_set, marker S>:
    have fn selected_constant by exist!:
        ? forall seed S:
            exist! value \ConstantFunctions<S, marker> st {$is_constant(S, marker, value)}
        have fn candidate(x S) S = marker
        forall x S:
            candidate(x) = marker
        by def $is_constant(S, marker, candidate)
        candidate $in \ConstantFunctions<S, marker>
        witness exist value \ConstantFunctions<S, marker> st {$is_constant(S, marker, value)} from candidate
        claim:
            ? forall value1, value2 \ConstantFunctions<S, marker>:
                $is_constant(S, marker, value1)
                $is_constant(S, marker, value2)
                =>:
                    value1 = value2
            claim:
                ? forall x S:
                    value1(x) = value2(x)
                value1(x) = marker = value2(x)
            $fn_eq(value1, value2)
            value1 = value2

forall S nonempty_set, marker, seed, x S:
    $is_constant(S, marker, \selected_constant<S, marker>(seed))
    \selected_constant<S, marker>(seed)(x) = marker
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "template_choice_returning_refined_function_remains_callable",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "a selected value in a refined function carrier must remain callable:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn set_alias_to_fn_set_is_nonempty_and_registers_function_type() {
    let source_code = r#"
have T set = fn(i1 closed_range(1, 3), j closed_range(1, 3), k closed_range(1, 3)) R
have A T
A(1, 2, 3) $in R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "set_alias_to_fn_set_is_nonempty_and_registers_function_type",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "set_alias_to_fn_set_is_nonempty_and_registers_function_type failed:\n{}",
        run_output
    );
}

#[test]
fn template_set_alias_to_fn_set_is_nonempty_and_registers_function_type() {
    let source_code = r#"
template<S set, n N_pos>:
    have tensor3 set = fn(i1 closed_range(1, n), j closed_range(1, n), k closed_range(1, n)) S

have A \tensor3<R, 3>
A(1, 2, 3) $in R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "template_set_alias_to_fn_set_is_nonempty_and_registers_function_type",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "template_set_alias_to_fn_set_is_nonempty_and_registers_function_type failed:\n{}",
        run_output
    );
}

#[test]
fn weak_order_does_not_recursively_prove_equality() {
    let source_code = r#"
have a, b R
trust a <= b
a = b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("weak_order_does_not_recursively_prove_equality");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "recursive equality/order proof should fail, but succeeded:\n{}",
        run_output
    );
}

#[test]
fn two_known_weak_order_directions_prove_equality() {
    let source_code = r#"
have a, b R
trust a <= b
trust b <= a
a = b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("two_known_weak_order_directions_prove_equality");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known weak-order facts should prove equality by antisymmetry:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"rule\": \"equality from a >= b and b >= a\""),
        "weak-order equality should report its builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn real_line_comparison_exist_witnesses_are_builtin_rules() {
    let source_code = r#"
have above R:
    above > 100
have below R:
    100 > below
have equal_to R:
    equal_to = 100
have distinct_from R:
    100 != distinct_from
exist a, b R st {a >= b}
exist a, b R st {b <= a}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "real_line_comparison_exist_witnesses_are_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "real-line comparison witnesses should verify without std facts:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"builtin rule\"")
            && run_output.contains("exist: real-line comparison witness"),
        "real-line comparison witnesses should expose builtin provenance:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"type\": \"cite forall fact\""),
        "real-line comparison witnesses must not cite a source-level forall:\n{}",
        run_output
    );
}

#[test]
fn archimedean_reciprocal_bound_is_a_builtin_rule() {
    let source_code = r#"
forall epsilon R_pos:
    exist n N_pos st {1 / n < epsilon}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("archimedean_reciprocal_bound_is_a_builtin_rule");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "the Archimedean reciprocal bound should verify without std facts:\n{}",
        run_output
    );
    assert!(
        run_output.contains("exist: Archimedean reciprocal bound"),
        "the Archimedean reciprocal bound should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn sufficiently_wide_real_intervals_have_integer_witnesses_as_builtin_rules() {
    let source_code = r#"
forall a, b R:
    a < b
    b - a > 1
    =>:
        exist c Z st {a < c < b}

forall a, b R:
    b - a >= 1
    =>:
        exist c Z st {a <= c <= b}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "sufficiently_wide_real_intervals_have_integer_witnesses_as_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "wide real intervals should have integer witnesses:\n{}",
        run_output
    );
    for rule in [
        "exist: integer strictly inside a real interval wider than 1",
        "exist: integer inside a real interval of length at least 1",
    ] {
        assert!(
            run_output.contains(rule),
            "missing integer interval builtin provenance `{}`:\n{}",
            rule,
            run_output
        );
    }

    let mut short_interval_runtime = Runtime::new();
    short_interval_runtime.new_file_path_new_env_new_name_scope(
        "strict_real_interval_without_length_bound_has_no_integer_builtin_witness",
    );
    let (short_interval_results, short_interval_error) = run_source_code(
        r#"
forall a, b R:
    a < b
    =>:
        exist c Z st {a < c < b}
"#,
        &mut short_interval_runtime,
    );
    let (short_interval_succeeded, short_interval_output) = render_run_source_code_output(
        &short_interval_runtime,
        &short_interval_results,
        &short_interval_error,
        false,
    );
    assert!(
        !short_interval_succeeded,
        "a real interval without a length bound must not get an integer witness:\n{}",
        short_interval_output
    );
}

#[test]
fn finite_set_size_zero_is_not_nonempty_is_a_builtin_rule() {
    let source_code = r#"
forall S finite_set:
    finite_set_size(S) = 0
    =>:
        not $is_nonempty_set(S)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "finite_set_size_zero_is_not_nonempty_is_a_builtin_rule",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "a zero-size finite set should be empty:\n{}",
        run_output
    );
    assert!(
        run_output.contains("finite set size zero is not nonempty"),
        "the zero-size finite-set rule should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn negation_reverses_order_as_a_builtin_rule() {
    let source_code = r#"
forall x R:
    x < -5
    =>:
        -x > 5
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("negation_reverses_order_as_a_builtin_rule");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "negation should reverse a strict order:\n{}",
        run_output
    );
    assert!(
        run_output.contains("order: -x > y from x < -y"),
        "negation reversal should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn positive_real_powers_reflect_order_as_builtin_rules() {
    let source_code = r#"
forall a, b, q R_pos:
    a^q < b^q
    =>:
        a < b

forall a, b, q R_pos:
    a^q <= b^q
    =>:
        a <= b
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "positive_real_powers_reflect_order_as_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "positive-real powers should reflect order on positive bases:\n{}",
        run_output
    );
    assert!(
        run_output.contains("a < b from positive bases and exponent, and a^q < b^q")
            && run_output.contains("a <= b from positive bases and exponent, and a^q <= b^q"),
        "the positive-power inverse rules should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn rational_integer_ratio_representation_is_a_builtin_rule() {
    let source_code = r#"
forall q Q:
    exist a Z, b Z_nz st {q = a / b}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "rational_integer_ratio_representation_is_a_builtin_rule",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "rational integer-ratio representation should verify without std facts:\n{}",
        run_output
    );
    assert!(
        run_output.contains("exist: rational integer ratio representation"),
        "rational representation should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn rational_integer_ratio_representation_requires_a_rational_target() {
    let source_code = r#"
exist a Z, b Z_nz st {sqrt(2) = a / b}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "rational_integer_ratio_representation_requires_a_rational_target",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "the rational representation builtin must not apply to arbitrary reals:\n{}",
        run_output
    );
}

#[test]
fn rational_reduced_fraction_representations_are_builtin_rules() {
    let source_code = r#"
forall a Q:
    exist p Z, q N_pos st {a = p / q, forall! z N_pos: p % z = 0 and q % z = 0 => {z = 1}}

forall a Q:
    exist p Z, q N_pos st {p / q = a, forall! z N_pos: 0 = q % z and 0 = p % z => {1 = z}}

forall a Q:
    exist! p Z, q N_pos st {a = p / q, forall! z N_pos: p % z = 0 and q % z = 0 => {z = 1}}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "rational_reduced_fraction_representations_are_builtin_rules",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "reduced rational fractions should verify without std facts:\n{}",
        run_output
    );
    assert!(
        run_output.contains("exist: rational reduced fraction with positive denominator"),
        "reduced rational fractions should expose builtin provenance:\n{}",
        run_output
    );
    assert!(
        run_output.contains("exist!: unique rational reduced fraction with positive denominator"),
        "unique reduced rational fractions should expose builtin provenance:\n{}",
        run_output
    );
}

#[test]
fn rational_reduced_fraction_builtin_rejects_nearby_shapes() {
    run_with_large_stack(
        "rational_reduced_fraction_builtin_rejects_nearby_shapes",
        || {
            let rules = [
                "exist: rational reduced fraction with positive denominator",
                "exist!: unique rational reduced fraction with positive denominator",
            ];
            for (label, source_code) in [
                (
                    "irrational_target",
                    r#"
exist p Z, q N_pos st {sqrt(2) = p / q, forall! z N_pos: p % z = 0 and q % z = 0 => {z = 1}}
"#,
                ),
                (
                    "wrong_unique_reducedness_conclusion",
                    r#"
forall a Q:
    exist! p Z, q N_pos st {a = p / q, forall! z N_pos: p % z = 0 and q % z = 0 => {z = 2}}
"#,
                ),
                (
                    "wrong_witness_carriers",
                    r#"
forall a Q:
    exist p N, q Z_nz st {a = p / q, forall! z N_pos: p % z = 0 and q % z = 0 => {z = 1}}
"#,
                ),
            ] {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(
                    format!("rational_reduced_fraction_builtin_rejects_{}", label).as_str(),
                );
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

                assert!(
                    !run_succeeded,
                    "{} must not receive a reduced-fraction builtin proof:\n{}",
                    label, run_output
                );
                assert!(
                    rules.iter().all(|rule| !run_output.contains(rule)),
                    "{} must not expose reduced-fraction builtin provenance:\n{}",
                    label,
                    run_output
                );
            }
        },
    );
}

#[test]
fn real_line_comparison_builtins_require_real_operands() {
    run_with_large_stack(
        "real_line_comparison_builtins_require_real_operands",
        || {
            let positive_source = r#"
have a, b R
a = b or a < b or a > b
a <= b or a >= b
a > b or a <= b
exist x R st {x = a}
exist x R st {x > a}
"#;
            let mut positive_runtime = Runtime::new();
            positive_runtime.new_file_path_new_env_new_name_scope(
                "real_line_comparison_builtins_require_real_operands_positive",
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
                "real-line comparison builtins should retain real examples:\n{}",
                positive_output
            );

            for (label, source_code) in [
                ("trichotomy", "have S, T set\nS = T or S < T or S > T"),
                ("comparability", "have S, T set\nS <= T or S >= T"),
                ("strict_non_strict_split", "have S, T set\nS > T or S <= T"),
                ("existence_equality", "have S set\nexist x R st {x = S}"),
                ("existence_order", "have S set\nexist x R st {x > S}"),
            ] {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(
                    format!(
                        "real_line_comparison_builtins_require_real_operands_{}",
                        label
                    )
                    .as_str(),
                );
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    !run_succeeded,
                    "{} must not apply a real-line rule to set operands:\n{}",
                    label, run_output
                );
            }
        },
    );
}

#[test]
fn zero_product_split_requires_real_factors() {
    let positive_source = r#"
have a, b R
trust a * b = 0
a = 0 or b = 0
"#;
    let mut positive_runtime = Runtime::new();
    positive_runtime
        .new_file_path_new_env_new_name_scope("zero_product_split_requires_real_factors_positive");
    let (positive_results, positive_error) =
        run_source_code(positive_source, &mut positive_runtime);
    let (positive_succeeded, positive_output) =
        render_run_source_code_output(&positive_runtime, &positive_results, &positive_error, false);
    assert!(
        positive_succeeded,
        "zero-product splitting should retain real factors:\n{}",
        positive_output
    );
    assert!(
        positive_output.contains("zero_product_split"),
        "zero-product splitting should expose its builtin provenance:\n{}",
        positive_output
    );

    let non_real_source = r#"
have A, B set
trust A * B = 0
A = 0 or B = 0
"#;
    let mut non_real_runtime = Runtime::new();
    non_real_runtime
        .new_file_path_new_env_new_name_scope("zero_product_split_requires_real_factors_non_real");
    let (non_real_results, non_real_error) =
        run_source_code(non_real_source, &mut non_real_runtime);
    let (non_real_succeeded, non_real_output) =
        render_run_source_code_output(&non_real_runtime, &non_real_results, &non_real_error, false);
    assert!(
        !non_real_succeeded,
        "a non-real product must not become a zero-product premise:\n{}",
        non_real_output
    );
}

#[test]
fn known_forall_existential_matching_requires_exact_atomic_relation() {
    let equality_as_inequality = r#"
trust:
    forall a Z:
        exist b Z st {b = a}
have chosen Z:
    chosen != 100
"#;
    let mut equality_runtime = Runtime::new();
    equality_runtime.new_file_path_new_env_new_name_scope(
        "known_forall_existential_matching_rejects_equality_as_inequality",
    );
    let (equality_results, equality_error) =
        run_source_code(equality_as_inequality, &mut equality_runtime);
    let (equality_succeeded, equality_output) =
        render_run_source_code_output(&equality_runtime, &equality_results, &equality_error, false);
    assert!(
        !equality_succeeded,
        "an equality witness must not verify a distinctness witness:\n{}",
        equality_output
    );

    let positive_as_negative = r#"
abstract_prop p(x)
trust:
    forall a Z:
        exist b Z st {$p(b)}
have chosen Z:
    not $p(chosen)
"#;
    let mut predicate_runtime = Runtime::new();
    predicate_runtime.new_file_path_new_env_new_name_scope(
        "known_forall_existential_matching_rejects_positive_as_negative",
    );
    let (predicate_results, predicate_error) =
        run_source_code(positive_as_negative, &mut predicate_runtime);
    let (predicate_succeeded, predicate_output) = render_run_source_code_output(
        &predicate_runtime,
        &predicate_results,
        &predicate_error,
        false,
    );
    assert!(
        !predicate_succeeded,
        "a positive predicate witness must not verify a negated witness:\n{}",
        predicate_output
    );

    let exact_equality = r#"
trust:
    forall a Z:
        exist b Z st {b = a}
have chosen Z:
    chosen = 100
"#;
    let mut exact_runtime = Runtime::new();
    exact_runtime.new_file_path_new_env_new_name_scope(
        "known_forall_existential_matching_still_accepts_exact_equality",
    );
    let (exact_results, exact_error) = run_source_code(exact_equality, &mut exact_runtime);
    let (exact_succeeded, exact_output) =
        render_run_source_code_output(&exact_runtime, &exact_results, &exact_error, false);
    assert!(
        exact_succeeded,
        "an exact existential relation should still instantiate:\n{}",
        exact_output
    );
}

#[test]
fn known_forall_instantiation_fills_middle_param_from_dom_facts() {
    run_with_large_stack(
        "known_forall_instantiation_fills_middle_param_from_dom_facts",
        || {
            let source_code = r#"
abstract_prop rel(X, x, y)

trust forall X set, x, y, z X:
    $rel(X, x, y)
    $rel(X, y, z)
    =>:
        $rel(X, x, z)

thm use_rel_trans_like:
    ? forall X set, a, b, c X:
        $rel(X, a, b)
        $rel(X, b, c)
        =>:
            $rel(X, a, c)
    $rel(X, a, c)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "known_forall_instantiation_fills_middle_param_from_dom_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "known forall instantiation should infer a middle parameter from known premises:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn zero_product_cancellation_does_not_recursively_reenter_equality() {
    let source_code = r#"
have a, b, k1, k2 N
trust:
    k1 = 0
    b = a * k1
b = a * k1 = a * 0 = 0
0 * k2 = 0
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "zero_product_cancellation_does_not_recursively_reenter_equality",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "zero-product cancellation recursion regression failed:\n{}",
        run_output
    );
}

#[test]
fn exist_unique_infers_component_uniqueness_forall() {
    let source_code = r#"
abstract_prop p(a, b)
trust exist! a, b R st {$p(a, b)}
forall a1, b1, a2, b2 R:
    $p(a1, b1)
    $p(a2, b2)
    =>:
        a1 = a2 and b1 = b2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("exist_unique_infers_component_uniqueness_forall");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "exist! component uniqueness inference failed:\n{}",
        run_output
    );
}

#[test]
fn exist_unique_component_uniqueness_proves_split_then_facts() {
    let source_code = r#"
abstract_prop p(a, b)
trust exist! a, b R st {$p(a, b)}
forall a1, b1, a2, b2 R:
    $p(a1, b1)
    $p(a2, b2)
    =>:
        a1 = a2
        b1 = b2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "exist_unique_component_uniqueness_proves_split_then_facts",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "component uniqueness from exist! should prove split then-facts:\n{}",
        run_output
    );
}

#[test]
fn exist_unique_still_accepts_tuple_uniqueness_forall() {
    let source_code = r#"
sketch:
    abstract_prop p(a, b)
    trust:
        exist a, b R st {$p(a, b)}
        forall a1, b1, a2, b2 R:
            $p(a1, b1)
            $p(a2, b2)
            =>:
                (a1, b1) = (a2, b2)
    exist! a, b R st {$p(a, b)}
"#;

    let mut runtime = Runtime::new();
    runtime
        .new_file_path_new_env_new_name_scope("exist_unique_still_accepts_tuple_uniqueness_forall");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "tuple-style uniqueness should still prove exist!:\n{}",
        run_output
    );
}

#[test]
fn have_fn_by_exist_accepts_question_goal_target() {
    run_with_large_stack("have_fn_by_exist_accepts_question_goal_target", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set
trust forall x A:
    exist! y B st {$F(x, y)}

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("have_fn_by_exist_accepts_question_goal_target");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "have fn by exist! prove target should succeed:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_prove_body_can_establish_target() {
    run_with_large_stack("have_fn_by_exist_prove_body_can_establish_target", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}
    trust exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "have_fn_by_exist_prove_body_can_establish_target",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "have fn by exist! proof body should establish the target forall:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_rebinds_value_dependent_function_signature() {
    run_with_large_stack(
        "have_fn_by_exist_rebinds_value_dependent_function_signature",
        || {
            let source_code = r#"
have fn interval_identity by exist!:
    ? forall a, b R, x '[a, b]:
        a <= b
        =>:
            exist! y R st {y = x}
    witness exist y R st {y = x} from x:
        x = x
    forall y1, y2 R:
        y1 = x
        y2 = x
        =>:
            y1 = x = y2
    exist! y R st {y = x}

forall a, b R, x '[a, b]:
    a <= b
    =>:
        interval_identity(a, b, x) = x

have fn dependent_function_value by exist!:
    ? forall a, b R, f fn(t '[a, b]) R, x '[a, b]:
        exist! y R st {y = f(x)}
    witness exist y R st {y = f(x)} from f(x):
        f(x) = f(x)
    forall y1, y2 R:
        y1 = f(x)
        y2 = f(x)
        =>:
            y1 = f(x) = y2
    exist! y R st {y = f(x)}

forall a, b R, f fn(t '[a, b]) R, x '[a, b]:
    dependent_function_value(a, b, f, x) = f(x)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_exist_rebinds_value_dependent_function_signature",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have fn by exist! should rebind forall parameters into its stored function signature:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_fn_by_exist_releases_unique_witness_direction() {
    run_with_large_stack("have_fn_by_exist_releases_unique_witness_direction", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y)}
    trust exist! y B st {$F(x, y)}

forall x A, y B:
    $F(x, y)
    =>:
        y = f(x)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "have_fn_by_exist_releases_unique_witness_direction",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "have fn by exist! should release the unique witness direction:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_caches_alpha_equivalent_uniqueness_forall() {
    run_with_large_stack(
        "have_fn_by_exist_caches_alpha_equivalent_uniqueness_forall",
        || {
            let source_code = r#"
abstract_prop F(x, y)
abstract_prop P(x)

have fn f by exist!:
    ? forall x R:
        exist! y R st {$F(x, y)}
    trust exist! y R st {$F(x, y)}

trust forall z R:
    forall u R, v R:
        $F(u, v)
        =>:
            v = f(u)
    =>:
        $P(z)

$P(0)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_exist_caches_alpha_equivalent_uniqueness_forall",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have fn by exist! should cache its generated uniqueness forall modulo binder names:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_fn_by_exist_unique_witness_direction_keeps_all_body_facts() {
    run_with_large_stack(
        "have_fn_by_exist_unique_witness_direction_keeps_all_body_facts",
        || {
            let source_code = r#"
abstract_prop F(x, y)
abstract_prop G(x, y)
have A set
have B set

have fn f by exist!:
    ? forall x A:
        exist! y B st {$F(x, y), $G(x, y)}
    trust exist! y B st {$F(x, y), $G(x, y)}

forall x A, y B:
    $F(x, y)
    $G(x, y)
    =>:
        y = f(x)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_exist_unique_witness_direction_keeps_all_body_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "have fn by exist! uniqueness direction should keep every exist! body fact:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_fn_by_exist_requires_question_goal() {
    run_with_large_stack("have_fn_by_exist_requires_question_goal", || {
        let source_code = r#"
abstract_prop F(x, y)
have A set
have B set
trust forall x A:
    exist! y B st {$F(x, y)}

have fn f by exist!:
    forall x A:
        exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("have_fn_by_exist_requires_question_goal");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "direct forall form should be rejected:\n{}",
            run_output
        );
        assert!(
            run_output.contains("expects a `? forall ...` goal block"),
            "direct forall rejection should report the expected goal shape:\n{}",
            run_output
        );
    });
}

#[test]
fn have_fn_by_exist_question_goal_requires_forall_target() {
    run_with_large_stack(
        "have_fn_by_exist_question_goal_requires_forall_target",
        || {
            let source_code = r#"
have fn f by exist!:
    ? 1 = 1
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "have_fn_by_exist_question_goal_requires_forall_target",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "non-forall prove target should fail:\n{}",
                run_output
            );
            assert!(
                run_output.contains("goal must be a single `forall` fact"),
                "non-forall prove target should report the expected shape:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn elementary_set_elimination_and_subset_rules_are_builtin() {
    let source_code = r#"
have A, B, x set
trust x $in union(A, B)
x $in A or x $in B

trust not x $in A
not x $in intersect(A, B)

intersect(A, B) $subset A
intersect(A, B) $subset B
A $subset union(A, B)
B $subset union(A, B)
set_minus(A, B) $subset A
set_diff(A, B) = union(set_minus(A, B), set_minus(B, A))

trust B $subset A
B = set_minus(A, set_minus(A, B))
set_minus(A, set_minus(A, B)) = B

forall F finite_set, c set:
    c $subset F
    =>:
        c = set_minus(F, set_minus(F, c))
        $is_finite_set(set_minus(F, set_minus(F, c)))
        $is_finite_set(c)
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "elementary_set_elimination_and_subset_rules_are_builtin",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "elementary set rules should verify without std facts:\n{}",
        run_output
    );
    for rule in [
        "intersection non-membership: non-member of the left side",
        "intersection subset operand",
        "operand subset union",
        "set minus subset left operand",
        "set diff as union of asymmetric differences",
        "set minus recovers subset from relative complement",
    ] {
        assert!(
            run_output.contains(rule),
            "missing builtin rule `{rule}`:\n{}",
            run_output
        );
    }
}

#[test]
fn set_minus_relative_complement_requires_subset() {
    let source_code = r#"
have A, B set
B = set_minus(A, set_minus(A, B))
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("set_minus_relative_complement_requires_subset");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "relative-complement recovery must require a subset premise:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("set minus recovers subset from relative complement"),
        "the builtin rule must not apply without a subset premise:\n{}",
        run_output
    );
}

#[test]
fn distinct_template_struct_memberships_expand_distinct_field_views() {
    run_with_large_stack(
        "distinct_template_struct_memberships_expand_distinct_field_views",
        || {
            let source_code = r#"
struct Family<U nonempty_set, m N_pos>:
    carriers finite_seq(power_set(U), m)
    zeros finite_seq(U, m)

prop is_family(U nonempty_set, m N_pos, family &Family<U, m>):
    forall k N_pos:
        k <= m
        =>:
            $is_nonempty_set(family.carriers(k))
            family.zeros(k) $in family.carriers(k)

prop is_dual_family(U nonempty_set, m N_pos, original &Family<U, m>, dual &Family<fn(u U) R, m>):
    $is_family(U, m, original)
    $is_family(fn(u U) R, m, dual)

template<U nonempty_set, m N_pos, original &Family<U, m>: $is_family(U, m, original)>:
    trust have selected_family &Family<fn(u U) R, m>:
        $is_dual_family(U, m, original, selected_family)

trust have original &Family<R, 2>:
    $is_family(R, 2, original)
trust $is_dual_family(R, 2, original, \selected_family<R, 2, original>)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "distinct_template_struct_memberships_expand_distinct_field_views",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "each selected struct object needs its own callable field view:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn have_equal_object_transports_across_equal_struct_indices() {
    let source_code = r#"
struct IndexedBox<A nonempty_set, n N>:
    value A
    stored_index N
    entry fn(slot closed_range(0, n)) A

thm equal_index_transport:
    ? forall A nonempty_set, m, n N, x &IndexedBox<A, n>:
        m = n
        =>:
            exist y &IndexedBox<A, m> st {y = x}
    have transported &IndexedBox<A, m> = x
    transported.value = x.value
    transported.stored_index = x.stored_index
    claim:
        ? forall index closed_range(0, m):
            transported.entry(index) = x.entry(index)
        index <= n
        transported.entry(index) = x.entry(index)
    witness exist y &IndexedBox<A, m> st {y = x} from transported
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "have_equal_object_transports_across_equal_struct_indices",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known equality of struct indices should transport membership in the indexed carrier:\n{}",
        run_output
    );
}
