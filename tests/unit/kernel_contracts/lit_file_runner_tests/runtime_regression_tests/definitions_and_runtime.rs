use super::*;
use crate::test_support::execute_source;

#[test]
fn clear_is_an_ordinary_name_and_bare_clear_does_not_reset_the_environment() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("clear_is_an_ordinary_name");

    let (definition_results, definition_error) =
        execute_source("have clear R = 1\nclear = 1", &mut runtime);
    let (definition_succeeded, definition_output) =
        render_run_output(&runtime, &definition_results, &definition_error);
    assert!(
        definition_succeeded,
        "clear should be accepted as an ordinary definition name:\n{}",
        definition_output
    );

    let (bare_results, bare_error) = execute_source("clear", &mut runtime);
    let (bare_succeeded, bare_output) = render_run_output(&runtime, &bare_results, &bare_error);
    assert!(bare_results.is_empty());
    assert!(
        !bare_succeeded,
        "bare clear must be parsed as an ordinary fact and rejected, not executed:\n{}",
        bare_output
    );

    let (after_results, after_error) = execute_source("clear = 1", &mut runtime);
    let (after_succeeded, after_output) = render_run_output(&runtime, &after_results, &after_error);
    assert!(
        after_succeeded,
        "a rejected bare clear must not reset existing definitions:\n{}",
        after_output
    );
}

#[test]
fn ordinary_prop_proof_still_requires_parameter_constraints() {
    let source_code = r#"
prop natural_only(n N):
    n = n

$natural_only(-1)
"#;
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("inferred_prop_definition_argument_types");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "an ordinary proof cannot establish a prop whose parameter constraint is false:\n{}",
        run_output
    );
}

#[test]
fn ordinary_atomic_verification_uses_a_concrete_prop_definition() {
    run_with_large_stack("automatic_prop_definition", || {
        let source_code = r#"
prop unit_pair(x R, y R):
    x = 1
    y = 1

$unit_pair(1, 1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("automatic_prop_definition");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "ordinary atomic verification should use the concrete definition:\n{}",
            run_output
        );
        assert!(runtime.cache_known_facts_contains("$unit_pair(1, 1)").0);
    });
}

#[test]
fn witnessed_definition_clause_automatically_packages_the_concrete_prop() {
    run_with_large_stack("automatic_existential_definition_packaging", || {
        let source_code = r#"
prop even(n N):
    exist k N st {n = 2 * k}

thm even_mul:
    ? forall m, n N:
        $even(n)
        =>:
            $even(m * n)
    obtain k from exist k N st {n = 2 * k}
    witness exist l N st {m * n = 2 * l} from m * k:
        m * n = m * (2 * k) = 2 * (m * k)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("automatic_existential_definition_packaging");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "an exact witnessed definition clause should package its concrete prop:\n{}",
            run_output
        );
        assert!(run_output.contains("$even(m * n)"));
    });
}

#[test]
fn by_def_strictly_checks_and_stores_a_concrete_prop() {
    run_with_large_stack("by_def_strict_success", || {
        let source_code = r#"
prop unit_pair(x R, y R):
    x = 1
    y = 1

1 = 1
by def $unit_pair(1, 1)
$unit_pair(1, 1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("by_def_strict_success");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(run_succeeded, "by def should succeed:\n{}", run_output);
        assert!(run_output.contains("\"kind\": \"ByDefStmt\""));
        assert!(run_output.contains("\"kind\": \"SuccessVerifyByDefinitionResult\""));
        assert!(run_output.contains("\"definition_clause_facts\":"));
        assert!(runtime.cache_known_facts_contains("$unit_pair(1, 1)").0);
    });
}

#[test]
fn by_def_accepts_inline_and_canonicalizes_block_goal_form() {
    run_with_large_stack("by_def_inline_and_block", || {
        let source_code = r#"
by def {1} $subset {1, 2}
by def:
    ? {2} $subset {1, 2}
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("by_def_inline_and_block");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);
        assert!(
            run_succeeded,
            "inline and block by def forms should share definition verification:\n{}",
            run_output
        );
        assert!(runtime.cache_known_facts_contains("{1} $subset {1, 2}").0);
        assert!(runtime.cache_known_facts_contains("{2} $subset {1, 2}").0);
        assert!(run_output.contains("\"statement\": \"by def {1} $subset {1, 2}\""));
        assert!(run_output.contains("\"statement\": \"by def {2} $subset {1, 2}\""));
        assert!(!run_output.contains("by def:\\n"));
    });
}

#[test]
fn inline_by_def_keeps_the_supported_definition_boundary() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("inline_by_def_unsupported_fact");
    let (stmt_results, runtime_error) = execute_source("by def 1 = 1", &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    assert!(
        !run_succeeded,
        "inline by def must not turn an arbitrary atomic fact into a definition:\n{}",
        run_output
    );
    assert!(
        run_output.contains("has no supported builtin definition"),
        "the failure should retain the existing definition boundary:\n{}",
        run_output
    );
}

#[test]
fn by_def_resolves_an_explicit_current_module_prop() {
    run_with_large_stack("by_def_module_qualified", || {
        let source_code = r#"
prop unit(x R):
    x = 1
1 = 1
by def $Current::unit(1)
$Current::unit(1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("by_def_module_qualified");
        runtime.current_module_mut().module_name = "Current".to_string();
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "module-qualified by def should succeed:\n{}",
            run_output
        );
        assert!(run_output.contains("by def $Current::unit(1)"));
    });
}

#[test]
fn by_def_does_not_short_circuit_on_an_already_known_target() {
    run_with_large_stack("by_def_known_target_strictness", || {
        let source_code = r#"
prop is_zero(x R):
    x = 0
trust $is_zero(1)
by def $is_zero(1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("by_def_known_target_strictness");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "by def should recheck the definition:\n{}",
            run_output
        );
        assert!(run_output.contains("\"definition_clause_facts\": ["));
        assert!(run_output.contains("\"statement\": \"1 = 0\""));
    });
}

#[test]
fn failed_by_def_does_not_store_its_target() {
    run_with_large_stack("by_def_failure_is_atomic", || {
        let source_code = r#"
prop is_zero(x R):
    x = 0
by def $is_zero(1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("by_def_failure_is_atomic");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(!run_succeeded, "fixture should fail:\n{}", run_output);
        assert!(run_output.contains("definition clause 1 is not verified: `1 = 0`"));
        assert!(!runtime.cache_known_facts_contains("$is_zero(1)").0);
    });
}

#[test]
fn by_def_rejects_non_concrete_or_empty_definitions() {
    run_with_large_stack("by_def_rejects_invalid_definitions", || {
        let cases = [
            (
                "abstract",
                "abstract_prop P(x)\nby def $P(1)",
                "is an abstract_prop and has no concrete definition body",
            ),
            (
                "empty",
                "prop P(x R)\nby def $P(1)",
                "has no definition clauses",
            ),
            (
                "missing",
                "by def $P(1)",
                "concrete prop definition `P` was not found",
            ),
        ];

        for (label, source_code, expected) in cases {
            let mut runtime = Runtime::default();
            runtime.start_isolated_source(format!("by_def_{}", label).as_str());
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);
            assert!(!run_succeeded, "{} should fail:\n{}", label, run_output);
            assert!(run_output.contains(expected), "{}:\n{}", label, run_output);
        }
    });
}

#[test]
fn by_def_accepts_explicit_builtin_definitions() {
    run_with_large_stack("by_def_builtin_definitions", || {
        let source_code = r#"
by def {1} $subset {1, 2}
by def {1, 2} $superset {1}
by def $proper_subset({1}, {1, 2})
by def {1, 2} $proper_superset {1}

have fn singleton_identity(x {1}) {1} = x
by def $injective({1}, {1}, singleton_identity)
trust forall y {1}:
    exist x {1} st {y = singleton_identity(x)}
by def $surjective({1}, {1}, singleton_identity)
by def $bijective({1}, {1}, singleton_identity)

have fn real_identity(x R) R = x
have fn second_real_identity(x R) R = x
by def $fn_eq_in(real_identity, second_real_identity, R)
by def $fn_eq(real_identity, second_real_identity)
"#;
        let mut runtime = Runtime::default();
        runtime.start_isolated_source("by_def_builtin_definitions");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);
        assert!(
            run_succeeded,
            "builtin definitions should verify explicitly:\n{run_output}"
        );
        assert!(run_output.contains("\"kind\": \"ByDefStmt\""));
        assert!(run_output.contains("\"kind\": \"SuccessVerifyByDefinitionResult\""));
        assert!(run_output.contains("\"definition_clauses\": ["));
        assert!(!run_output.contains("builtin definition of `"));
    });
}

#[test]
fn by_def_reports_argument_count_and_type_failures() {
    run_with_large_stack("by_def_argument_failures", || {
        let cases = [
            (
                "arity",
                "prop P(x R, y R):\n    x = y\nby def $P(1)",
                "expected 2 argument(s), got 1",
            ),
            (
                "type",
                "prop P(x N):\n    x = x\nby def $P(-1)",
                "could not verify argument parameter types",
            ),
        ];

        for (label, source_code, expected) in cases {
            let mut runtime = Runtime::default();
            runtime.start_isolated_source(format!("by_def_{}", label).as_str());
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);
            assert!(!run_succeeded, "{} should fail:\n{}", label, run_output);
            assert!(run_output.contains(expected), "{}:\n{}", label, run_output);
        }
    });
}

#[test]
fn prop_definition_instantiation_freshens_a_caller_name_collision() {
    run_with_large_stack("prop_definition_binder_freshening", || {
        let source_code = r#"
prop holds_for_all(n N):
    forall s set:
        n = n

claim:
    ? forall s set, n N:
        $holds_for_all(n)
    by def $holds_for_all(n)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("prop_definition_binder_freshening");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "a stored definition binder should be freshened at the call site:\n{}",
            run_output
        );
        assert!(run_output.contains("$holds_for_all(n)"));
    });
}

#[test]
fn obtain_from_exist_preserves_the_existential_binder_identity() {
    run_with_large_stack("obtain_existential_binder_identity", || {
        let source_code = r#"
by contra:
    ? not exist x R st {x != x}
    obtain a from exist x R st {x != x}
    impossible a = a
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("obtain_existential_binder_identity");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "existential elimination should release the instantiated body fact:\n{}",
            run_output
        );
    });
}

#[test]
fn known_set_equality_transports_across_alpha_equivalent_set_builders() {
    run_with_large_stack("set_builder_equality_alpha_transport", || {
        let source_code = r#"
by contra:
    ? {a N: a % 4 = 0} != {a N: a % 2 = 0}
    release thm set_builder_member(2, {b N: b % 2 = 0})
    2 $in {c N: c % 4 = 0}
    impossible 2 % 4 = 0
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("set_builder_equality_alpha_transport");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "known equality should transport membership through alpha-equivalent binders:\n{}",
            run_output
        );
    });
}

#[test]
fn direct_known_equality_precedes_builtin_fallback() {
    let source_code = r#"
have a R
have b R
have c R
trust a = b
trust b = c
a = c
1 + 1 = 2
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("direct_known_equality_precedes_builtin_fallback");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "known equality should short-circuit while new arithmetic still reaches builtin rules:\n{}",
        run_output
    );
    assert!(
        run_output.contains("known-only equality: same known equality class"),
        "the transitive equality must use the direct known-equality path:\n{}",
        run_output
    );
}

#[test]
fn known_equality_closure_keeps_cross_environment_bridges() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("known_equality_closure_keeps_cross_environment_bridges");

    let a: Obj = Identifier::new("a".to_string()).into();
    let b: Obj = Identifier::new("b".to_string()).into();
    let c: Obj = Identifier::new("c".to_string()).into();
    runtime
        .top_level_env()
        .store_equality(&EqualFact::new(a.clone(), b.clone(), default_line_file()))
        .unwrap();

    let local_result: Result<(), RuntimeError> = runtime.run_in_local_env(|rt| {
        rt.top_level_env()
            .store_equality(&EqualFact::new(b, c, default_line_file()))?;
        let closure = rt.get_all_objs_equal_to_given(&obj_equality_key(&a));
        assert!(closure.contains(&"c".to_string()));
        Ok(())
    });
    local_result.unwrap();
}

#[test]
fn positive_real_power_closure_enables_log_inverse() {
    let source_code = r#"
forall a R+, x R:
    a^x $in R+

forall a R+, x, y R:
    a^x = y
    =>:
        y $in R+

forall a R+, x, y R:
    a != 1
    a^x = y
    =>:
        x = log(a, y)
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("positive_real_power_closure_enables_log_inverse");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "positive_real_power_closure_enables_log_inverse failed:\n{}",
        run_output
    );
    assert!(run_output.contains("R+: a^x from 0 < a and x in R"));
    assert!(run_output.contains("equality: log(a, b) = c from a^c = b"));
}

#[test]
fn forall_iff_output_reports_direction_checks() {
    let source_code = r#"
forall a, b R+, c R:
    a != 1
    =>:
        log(a, b) = c
    <=>:
        a^c = b
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("forall_iff_output_reports_direction_checks");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "forall_iff_output_reports_direction_checks failed:\n{}",
        run_output
    );
    assert!(run_output.contains("forall iff: then=>iff and iff=>then verified"));
    assert!(!run_output.contains("\"kind\": \"KnownForallInstantiation\""));
}

#[test]
fn forall_iff_well_definedness_checks_both_directions_independently() {
    let invalid_sources = [
        r#"
trust forall x R:
    =>:
        x != 0
    <=>:
        1 / x = 1 / x
"#,
        r#"
trust forall x R:
    =>:
        1 / x = 1 / x
    <=>:
        x != 0
"#,
    ];

    for (index, source_code) in invalid_sources.iter().enumerate() {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source(
            format!("forall_iff_independent_well_definedness_{}", index).as_str(),
        );
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            !run_succeeded,
            "an iff direction must not borrow its opposite side's assumptions:\n{}",
            run_output
        );
        assert!(run_output.contains("divisor `x` must be non-zero"));
    }
}

#[test]
fn definition_namespaces_reject_same_spelling_across_kinds() {
    run_with_large_stack(
        "definition_namespaces_reject_same_spelling_across_kinds",
        definition_namespaces_reject_same_spelling_across_kinds_impl,
    );
}

fn definition_namespaces_reject_same_spelling_across_kinds_impl() {
    let source_code = r#"
have fn SharedName(x R) R = 1
have algo for SharedName(x):
    1
prop SharedName(x R)
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("definition_namespaces_reject_same_spelling_across_kinds");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "same spelling across definition kinds should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("NameAlreadyUsedError"));
    assert!(run_output.contains("name `SharedName` is already used"));
}

#[test]
fn completed_binder_scope_releases_its_spelling_for_a_global_definition() {
    let source_code = r#"
forall x R:
    x = x

have x R = 1
x = 1
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source(
        "completed_binder_scope_releases_its_spelling_for_a_global_definition",
    );
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "a completed binder scope should release its spelling:\n{}",
        run_output
    );
}

#[test]
fn local_binder_cannot_shadow_a_visible_global_symbol() {
    let source_code = r#"
have x R = 1
forall x R:
    x = x
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("local_binder_cannot_shadow_a_visible_global_symbol");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "a local binder must not shadow a visible global:\n{}",
        run_output
    );
    assert!(run_output.contains("name `x` is already active"));
}

#[test]
fn nested_binders_cannot_reuse_a_spelling_across_binder_forms() {
    let source_code = r#"
forall x R:
    exist x R st {x = x}
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("nested_binders_cannot_reuse_a_spelling_across_binder_forms");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "nested binders must not reuse a spelling:\n{}",
        run_output
    );
    assert!(run_output.contains("name `x` is already active"));
}

#[test]
fn sibling_binder_scopes_can_reuse_a_spelling() {
    let source_code = r#"
forall x R:
    x = x

forall x R:
    x = x
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("sibling_binder_scopes_can_reuse_a_spelling");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "sibling scopes should be allowed to reuse a spelling:\n{}",
        run_output
    );
}

#[test]
fn duplicate_definition_names_fail_in_their_namespace() {
    run_with_large_stack(
        "duplicate_definition_names_fail_in_their_namespace",
        duplicate_definition_names_fail_in_their_namespace_impl,
    );
}

fn duplicate_definition_names_fail_in_their_namespace_impl() {
    let cases = [
        ("prop", "prop dup_prop(x R)\nprop dup_prop(x R)"),
        (
            "abstract_prop",
            "abstract_prop dup_abstract(x)\nabstract_prop dup_abstract(x)",
        ),
        (
            "abstract_prop after prop",
            "prop dup_predicate(x R)\nabstract_prop dup_predicate(x)",
        ),
        (
            "prop after abstract_prop",
            "abstract_prop dup_predicate2(x)\nprop dup_predicate2(x R)",
        ),
        (
            "struct",
            "struct DupStruct:\n    value R\n    other R\nstruct DupStruct:\n    value R\n    other R",
        ),
        (
            "template",
            "template<s set>:\n    have DupTemplate set = s\ntemplate<s set>:\n    have DupTemplate set = s",
        ),
        (
            "function implementation",
            "have fn dup_algo(x R) R = 1\nhave algo for dup_algo(x):\n    1\nhave algo for dup_algo(x):\n    1",
        ),
    ];

    for (label, source_code) in cases {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source(format!("duplicate_definition_names_{}", label).as_str());
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            !run_succeeded,
            "duplicate {} definition should fail, but succeeded:\n{}",
            label, run_output
        );
        assert!(
            run_output.contains("already used") || run_output.contains("already active"),
            "duplicate {} definition should report the unified-name collision:\n{}",
            label,
            run_output
        );
    }
}

#[test]
fn unicode_prop_name_works() {
    run_with_large_stack("unicode_prop_name_works", || {
        let source_code = r#"
prop 是一(x R):
    x = 1
by def $是一(1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("unicode_prop_name_works");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "unicode prop names should work:\n{}",
            run_output
        );
    });
}

#[test]
fn unicode_object_name_works() {
    run_with_large_stack("unicode_object_name_works", || {
        let source_code = r#"
have 甲 R = 1
甲 = 1
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("unicode_object_name_works");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "unicode object names should work:\n{}",
            run_output
        );
    });
}

#[test]
fn unicode_thm_name_works() {
    run_with_large_stack("unicode_thm_name_works", || {
        let source_code = r#"
thm 自反等式:
    ? forall x R:
        x = x
    x = x
release thm 自反等式(1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("unicode_thm_name_works");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "unicode theorem names should work:\n{}",
            run_output
        );
    });
}

#[test]
fn unicode_cart_does_not_mean_numeric_multiplication() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("unicode_cart_is_not_numeric_multiplication");
    let (stmt_results, runtime_error) = execute_source("2 × 3 = 6", &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "Unicode × must remain Cartesian product syntax, not numeric multiplication:\n{}",
        run_output
    );
    assert!(
        run_output.contains("cart(2, 3)"),
        "the rejected expression should expose its canonical Cartesian-product meaning:\n{}",
        run_output
    );
}

#[test]
fn theorem_axiom_and_strategy_reject_multiple_names() {
    let cases = [
        "thm first, second:\n    ? forall x R:\n        x = x\n    x = x",
        "axiom first, second:\n    ? forall x R:\n        x = x",
        "strategy first, second:\n    ? forall x R:\n        x = x\n    x = x",
    ];
    for source_code in cases {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source("multiple_definition_names_rejected");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);
        assert!(
            !run_succeeded,
            "multiple definition names should fail:\n{}",
            run_output
        );
    }
}

#[test]
fn thm_definition_stores_forall_fact_for_known_forall_use() {
    run_with_large_stack(
        "thm_definition_stores_forall_fact_for_known_forall_use",
        || {
            let source_code = r#"
abstract_prop target_thm_prop(x)

thm use_target_thm:
    ? forall x R:
        x = 1
        =>:
            $target_thm_prop(x)

    trust $target_thm_prop(x)

$target_thm_prop(1)
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source("thm_definition_stores_forall_fact_for_known_forall_use");
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                run_succeeded,
                "thm definition should store ordinary forall matching facts:\n{}",
                run_output
            );
            assert!(runtime
                .get_thm_definition_by_name("use_target_thm")
                .is_some());
        },
    );
}

#[test]
fn thm_definition_can_still_be_released() {
    run_with_large_stack("thm_definition_can_still_be_released", || {
        let source_code = r#"
prop target_thm_prop(x R):
    x = 1

thm use_target_thm:
    ? forall x R:
        x = 1
        =>:
            $target_thm_prop(x)

    by def $target_thm_prop(x)

release thm use_target_thm(1)
$target_thm_prop(1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("thm_definition_can_still_be_released");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "thm should remain available through explicit release thm calls:\n{}",
            run_output
        );
    });
}

#[test]
fn release_thm_releases_instantiated_then_facts() {
    // Acceptance artifact: target/release/litex -isolated -graph -f
    // examples/01_proof_patterns/release_theorem_consequences.lit
    run_with_large_stack("release_thm_releases_instantiated_then_facts", || {
        let source_code = r#"
abstract_prop target_thm_prop(x)

thm use_target_thm:
    ? forall x R:
        x = 1
        =>:
            $target_thm_prop(x)

    trust $target_thm_prop(x)

release thm use_target_thm(1)
$target_thm_prop(1)
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("release_thm_releases_instantiated_then_facts");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "release thm should release the instantiated then-fact:\n{}",
            run_output
        );
    });
}

#[test]
fn by_thm_selected_fact_uses_temporary_expansion_and_commits_only_the_target() {
    run_with_large_stack(
        "by_thm_selected_fact_uses_temporary_expansion_and_commits_only_the_target",
        || {
            let source_code = r#"
abstract_prop selected_middle(x)
abstract_prop selected_sibling(x)
abstract_prop selected_target(x)

axiom selected_middle_to_target:
    ? forall x R:
        $selected_middle(x)
        =>:
            $selected_target(x)

thm selected_expand:
    ? forall x R:
        x = x
        =>:
            $selected_middle(x)
            $selected_sibling(x)

    # Trusted facts isolate this runtime scoping regression from predicate definitions.
    trust $selected_middle(x)
    trust $selected_sibling(x)

by thm selected_expand(1) => $selected_target(1)
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "by_thm_selected_fact_uses_temporary_expansion_and_commits_only_the_target",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                run_succeeded,
                "selected by thm should succeed:\n{run_output}"
            );
            assert!(runtime.cache_known_facts_contains("$selected_target(1)").0);
            assert!(!runtime.cache_known_facts_contains("$selected_middle(1)").0);
            assert!(!runtime.cache_known_facts_contains("$selected_sibling(1)").0);
        },
    );
}

#[test]
fn by_thm_selected_fact_failure_discards_the_temporary_expansion() {
    run_with_large_stack(
        "by_thm_selected_fact_failure_discards_the_temporary_expansion",
        || {
            let source_code = r#"
abstract_prop selected_middle(x)
abstract_prop selected_sibling(x)
abstract_prop selected_unproved(x)

thm selected_expand:
    ? forall x R:
        x = x
        =>:
            $selected_middle(x)
            $selected_sibling(x)

    # Trusted facts isolate this runtime scoping regression from predicate definitions.
    trust $selected_middle(x)
    trust $selected_sibling(x)

by thm selected_expand(1) => $selected_unproved(1)
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "by_thm_selected_fact_failure_discards_the_temporary_expansion",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                !run_succeeded,
                "unproved selected fact should fail:\n{run_output}"
            );
            assert!(run_output.contains(
                "selected fact `$selected_unproved(1)` is not verified after theorem application"
            ));
            assert!(!runtime.cache_known_facts_contains("$selected_middle(1)").0);
            assert!(!runtime.cache_known_facts_contains("$selected_sibling(1)").0);
            assert!(
                !runtime
                    .cache_known_facts_contains("$selected_unproved(1)")
                    .0
            );
        },
    );
}

#[test]
fn by_thm_selected_fact_must_be_well_defined_before_temporary_expansion() {
    run_with_large_stack(
        "by_thm_selected_fact_must_be_well_defined_before_temporary_expansion",
        || {
            let source_code = r#"
have selected_callable set

thm selected_signature:
    ? forall token R:
        token = 0
        =>:
            selected_callable $in fn(x R) R

    # This background signature is intentionally available only through the theorem.
    trust selected_callable $in fn(x R) R

by thm selected_signature(0) => selected_callable(1) = selected_callable(1)
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "by_thm_selected_fact_must_be_well_defined_before_temporary_expansion",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                !run_succeeded,
                "parent well-definedness should fail:\n{run_output}"
            );
            assert!(run_output.contains("is not well-defined in the parent environment"));
            assert!(
                !runtime
                    .cache_known_facts_contains("selected_callable $in fn(x R) R")
                    .0
            );
        },
    );
}

#[test]
fn strategy_definition_is_automatically_available_as_known_forall() {
    let source_code = r#"
abstract_prop target_strategy_prop(x)

strategy use_target_strategy:
    ? forall x R:
        x = 1
        =>:
            $target_strategy_prop(x)

    trust:
        forall y R:
            y = 1
            =>:
                $target_strategy_prop(y)

$target_strategy_prop(1)
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("strategy_definition_is_automatically_available_as_known_forall");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "strategy definition should publish an automatically matched forall:\n{}",
        run_output
    );
    let Some(StmtResult::Success(SuccessStmtResult::Fact(final_result))) = stmt_results.last()
    else {
        panic!("expected the final strategy-derived fact:\n{run_output}");
    };
    let SuccessFactProofResult::KnownForallInstantiation(instantiation) = final_result.proof()
    else {
        panic!("strategy use should be ordinary known-forall matching:\n{run_output}");
    };
    assert_eq!(
        instantiation.source_fact.to_string(),
        runtime
            .get_strategy_definition_by_name("use_target_strategy")
            .expect("strategy definition should remain named")
            .forall_fact
            .to_string()
    );
}

#[test]
fn strategy_definition_stores_forall_fact_for_known_forall_use() {
    let source_code = r#"
prop target_strategy_prop(x R):
    x = 1

strategy use_target_strategy:
    ? forall x R:
        x = 1
        =>:
            $target_strategy_prop(x)

    trust:
        forall y R:
            y = 1
            =>:
                $target_strategy_prop(y)

claim:
    ? forall z R:
        z = 1
        =>:
            $target_strategy_prop(z)
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("strategy_definition_stores_forall_fact_for_known_forall_use");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "strategy definition should store its proved forall for known-forall use:\n{}",
        run_output
    );
}

#[test]
fn retired_strategy_control_words_are_names_and_control_syntax_is_rejected() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("retired_strategy_control_words_are_names");
    let (stmt_results, runtime_error) = execute_source(
        "have use R = 1\nhave stop R = 2\nuse = 1\nstop = 2",
        &mut runtime,
    );
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    assert!(
        run_succeeded,
        "retired strategy-control words should be ordinary names:\n{}",
        run_output
    );

    for source_code in ["use strategy missing", "stop strategy missing"] {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source("retired_strategy_control_syntax");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);
        assert!(
            !run_succeeded,
            "retired strategy-control syntax should fail: `{source_code}`\n{run_output}"
        );
    }
}

#[test]
fn strategy_rejects_non_single_atomic_then_fact() {
    let cases = [
        (
            "multiple then facts",
            r#"
prop p(x R):
    x = 1

strategy bad_strategy:
    ? forall x R:
        x = 1
        =>:
            $p(x)
            x = 1
"#,
            "strategy: forall then-clause must contain exactly one fact",
        ),
        (
            "non atomic then fact",
            r#"
strategy bad_strategy:
    ? forall x R:
        x = 1
        =>:
            x = 1 and x = 1
"#,
            "strategy: forall then-clause fact must be atomic",
        ),
    ];

    for (label, source_code, expected_message) in cases {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source(format!("strategy_rejects_{}", label).as_str());
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            !run_succeeded,
            "strategy {} case should fail, but succeeded:\n{}",
            label, run_output
        );
        assert!(
            run_output.contains(expected_message),
            "strategy {} case should report `{}`:\n{}",
            label,
            expected_message,
            run_output
        );
    }
}

#[test]
fn strategy_rejects_non_atomic_dom_fact() {
    let source_code = r#"
prop p(x R):
    x = 1

strategy bad_strategy:
    ? forall x R:
        x = 1 and x = 1
        =>:
            $p(x)
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("strategy_rejects_non_atomic_dom_fact");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "strategy non-atomic dom fact should fail, but succeeded:\n{}",
        run_output
    );
    assert!(
        run_output.contains("strategy: forall dom-clause facts must be atomic"),
        "strategy non-atomic dom fact should report atomic dom requirement:\n{}",
        run_output
    );
}

#[test]
fn strategy_rejects_equal_then_fact() {
    let source_code = r#"
strategy bad_strategy:
    ? forall x R:
        x = 1
        =>:
            x = x
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("strategy_rejects_equal_then_fact");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "strategy equality then fact should fail, but succeeded:\n{}",
        run_output
    );
    assert!(
        run_output.contains("strategy: forall then-clause fact must not be an equality fact"),
        "strategy equality then fact should report equality restriction:\n{}",
        run_output
    );
}

#[test]
fn theorem_and_claim_reuse_prechecked_goal_well_definedness() {
    let source_code = r#"
thm prechecked_theorem_goals:
    ? forall x R:
        x = x
        x + 0 = x

claim:
    ? forall x R:
        x = x
        x + 0 = x
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("theorem_and_claim_reuse_prechecked_goal_well_definedness");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "prechecked theorem and claim goals should still verify:\n{}",
        run_output
    );
}

#[test]
fn prechecked_goal_well_definedness_replays_safe_function_application_facts() {
    let cases = [
        (
            "theorem",
            r#"
struct PrecheckedCylindricalPoint:
    r R
    theta R
    z R

have fn prechecked_locus(c R) power_set(&PrecheckedCylindricalPoint) = {p &PrecheckedCylindricalPoint: p[3] = c}

prop prechecked_horizontal_plane(S power_set(&PrecheckedCylindricalPoint)):
    exist a &PrecheckedCylindricalPoint st {S = prechecked_locus(a[3])}

thm prechecked_definition_goal:
    ? forall c R:
        $prechecked_horizontal_plane(prechecked_locus(c))
    have a &PrecheckedCylindricalPoint = (0, 0, c)
    a[3] = c
    witness exist p &PrecheckedCylindricalPoint st {prechecked_locus(c) = prechecked_locus(p[3])} from a:
        prechecked_locus(c) = prechecked_locus(a[3])
"#,
        ),
        (
            "claim",
            r#"
struct PrecheckedCylindricalPoint:
    r R
    theta R
    z R

have fn prechecked_locus(c R) power_set(&PrecheckedCylindricalPoint) = {p &PrecheckedCylindricalPoint: p[3] = c}

prop prechecked_horizontal_plane(S power_set(&PrecheckedCylindricalPoint)):
    exist a &PrecheckedCylindricalPoint st {S = prechecked_locus(a[3])}

claim:
    ? forall c R:
        $prechecked_horizontal_plane(prechecked_locus(c))
    have a &PrecheckedCylindricalPoint = (0, 0, c)
    a[3] = c
    witness exist p &PrecheckedCylindricalPoint st {prechecked_locus(c) = prechecked_locus(p[3])} from a:
        prechecked_locus(c) = prechecked_locus(a[3])
"#,
        ),
    ];

    for (label, source_code) in cases {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source(label);
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "{} should reuse safe function-application facts from its preflight:\n{}",
            label, run_output
        );
    }
}

#[test]
fn prechecked_goal_certificate_replays_materialized_template_atomic_forall_rules() {
    let source_code = r#"
template<S nonempty_set, combine fn(a, b S) S>:
    have fn prechecked_selected_pair by exist!:
        ? forall x S:
            exist! pair cart(S, S) st {pair = (x, x), combine(pair[1], pair[2]) = combine(x, x)}
        have candidate cart(S, S) = (x, x)
        witness exist pair cart(S, S) st {pair = (x, x), combine(pair[1], pair[2]) = combine(x, x)} from candidate:
            candidate[1] = x
            candidate[2] = x
            combine(candidate[1], candidate[2]) = combine(x, x)
        forall pair1, pair2 cart(S, S):
            pair1 = (x, x)
            combine(pair1[1], pair1[2]) = combine(x, x)
            pair2 = (x, x)
            combine(pair2[1], pair2[2]) = combine(x, x)
            =>:
                pair1 = pair2

thm prechecked_selected_pair_projection:
    ? forall S nonempty_set, combine fn(a, b S) S, x S:
        combine(\prechecked_selected_pair<S, combine>(x)[1], \prechecked_selected_pair<S, combine>(x)[2]) = combine(x, x)
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source(
        "prechecked_goal_certificate_replays_materialized_template_atomic_forall_rules",
    );
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "a prechecked selected-function application must retain its materialized forall property:\n{}",
        run_output
    );
}

#[test]
fn prechecked_goal_certificate_keeps_materialized_case_rule_premises() {
    let source_code = r#"
template<S nonempty_set, A power_set(S), default S>:
    have fn prechecked_case_value(x S) S by cases:
        case x $in A: x
        case not x $in A: default

thm prechecked_case_rule_still_requires_its_branch:
    ? forall S nonempty_set, A power_set(S), default S, x S:
        \prechecked_case_value<S, A, default>(x) = default
"#;

    let mut runtime = Runtime::default();
    runtime
        .start_isolated_source("prechecked_goal_certificate_keeps_materialized_case_rule_premises");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "replaying a materialized case equation must not erase its branch premise:\n{}",
        run_output
    );
    assert!(
        run_output.contains("cannot prove then-clause"),
        "the premise-free case equation should remain unknown during proof verification:\n{}",
        run_output
    );
}

#[test]
fn prechecked_goal_keeps_template_instantiations_alive_during_preflight() {
    let source_code = r#"
prop preflight_metric(X set, dist fn(x, y X) R):
    forall x, y X:
        dist(x, y) >= 0

template<X set, dist fn(x, y X) R, Y power_set(X)>:
    have fn preflight_restricted_distance(x, y Y) R = dist(x, y)

thm preflight_template_lifetime:
    ? forall X set, dist fn(x, y X) R, Y power_set(X):
        $preflight_metric(X, dist)
        =>:
            $preflight_metric(Y, \preflight_restricted_distance<X, dist, Y>)
    trust $preflight_metric(Y, \preflight_restricted_distance<X, dist, Y>)
"#;
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("preflight_template_lifetime");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "template definitions created by one checked goal must remain available for the complete preflight:\n{}",
        run_output
    );
}

#[test]
fn prechecked_goal_certificate_never_stores_the_goal_itself() {
    let cases = [
        (
            "theorem",
            r#"
abstract_prop prechecked_unproved(x)

thm prechecked_goal_is_not_a_proof:
    ? forall x set:
        $prechecked_unproved(x)
"#,
        ),
        (
            "claim",
            r#"
abstract_prop prechecked_unproved(x)

claim:
    ? forall x set:
        $prechecked_unproved(x)
"#,
        ),
    ];

    for (label, source_code) in cases {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source(label);
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            !run_succeeded,
            "{} preflight certificate must not prove its own goal:\n{}",
            label, run_output
        );
        assert!(
            run_output.contains("cannot prove then-clause"),
            "{} should fail at proof verification after successful preflight:\n{}",
            label,
            run_output
        );
    }
}

#[test]
fn proof_local_facts_cannot_repair_an_ill_defined_theorem_or_claim_goal() {
    let cases = [
        (
            "theorem",
            r#"
thm proof_local_typing_does_not_repair_the_header:
    ? forall f set:
        f(0) = f(0)
    trust f $in fn(n N) R
"#,
            "thm: forall fact is not well defined",
        ),
        (
            "claim",
            r#"
claim:
    ? forall f set:
        f(0) = f(0)
    trust f $in fn(n N) R
"#,
            "claim: fact is not well defined",
        ),
    ];

    for (label, source_code, expected_error) in cases {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source(label);
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            !run_succeeded,
            "proof-local facts must not repair an ill-defined {} goal:\n{}",
            label, run_output
        );
        assert!(
            run_output.contains(expected_error),
            "{} should fail during its well-definedness preflight:\n{}",
            label,
            run_output
        );
        assert!(
            run_output.contains("function `f` not defined"),
            "{} should preserve the ill-defined function diagnostic:\n{}",
            label,
            run_output
        );
    }
}

#[test]
fn known_forall_instantiation_cites_the_complete_multi_conclusion_source() {
    run_with_large_stack(
        "known_forall_instantiation_cites_the_complete_multi_conclusion_source",
        || {
            let source_code = r#"
abstract_prop first(x)
abstract_prop second(x)

axiom paired_source:
    ? forall x R:
        $first(x)
        $second(x)

$first(2)
$second(2)
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "known_forall_instantiation_cites_the_complete_multi_conclusion_source",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                run_succeeded,
                "one conclusion of a stored multi-conclusion forall should remain citeable:\n{}",
                run_output
            );

            let [.., first_statement_result, second_statement_result] = stmt_results.as_slice()
            else {
                panic!("expected both instantiated facts:\n{run_output}");
            };
            let StmtResult::Success(SuccessStmtResult::Fact(first_result)) = first_statement_result
            else {
                panic!("expected the first instantiated fact:\n{run_output}");
            };
            let StmtResult::Success(SuccessStmtResult::Fact(second_result)) =
                second_statement_result
            else {
                panic!("expected the second instantiated fact:\n{run_output}");
            };
            let SuccessFactProofResult::KnownForallInstantiation(first_instantiation) =
                first_result.proof()
            else {
                panic!("expected the first known-forall proof:\n{run_output}");
            };
            let SuccessFactProofResult::KnownForallInstantiation(second_instantiation) =
                second_result.proof()
            else {
                panic!("expected the second known-forall proof:\n{run_output}");
            };
            let source_text = second_instantiation.source_fact.to_string();
            assert!(source_text.contains("$first("), "{source_text}");
            assert!(source_text.contains("$second("), "{source_text}");
            assert_eq!(
                first_instantiation.source_fact_id, second_instantiation.source_fact_id,
                "both selected conclusions must cite the one complete source forall identity"
            );
            assert_eq!(
                first_instantiation.source_conclusion_location,
                ForallConclusionLocation::direct_then_fact(0),
                "the first target must retain the first direct conclusion location"
            );
            assert_eq!(
                second_instantiation.source_conclusion_location,
                ForallConclusionLocation::direct_then_fact(1),
                "the verifier must retain the selected conclusion, not rebuild a smaller forall"
            );
            assert_eq!(
                runtime
                    .known_fact_id_for_fact(&second_instantiation.source_fact)
                    .expect("source lookup should be well-defined"),
                Some(second_instantiation.source_fact_id),
                "the consumer must cite the FactId of the complete stored forall"
            );
        },
    );
}

#[test]
fn committed_local_proofs_can_repeat_a_nested_binder_fact() {
    run_with_large_stack(
        "committed_local_proofs_can_repeat_a_nested_binder_fact",
        || {
            let source_code = r#"
have fn finite_integer_sum(first, last Z, term fn(term_index Z) Z) Z by cases:
    case first <= last: sum(first, last, term)
    case first > last: 0

thm finite_integer_sum_shift:
    ? forall first, last Z, term fn(term_index_shift Z) Z:
        first <= last
        =>:
            finite_integer_sum(first, last, term) = finite_integer_sum(first - 1, last - 1, fn(shifted_index Z) Z {term(shifted_index + 1)})
    first - 1 <= last - 1
    finite_integer_sum(first, last, term) = sum(first, last, term)
    finite_integer_sum(first - 1, last - 1, fn(shifted_index Z) Z {term(shifted_index + 1)}) = sum(first - 1, last - 1, fn(shifted_index Z) Z {term(shifted_index + 1)})
    claim:
        ? forall source_index Z:
            term(source_index) = fn(lambda_index Z) Z {term(lambda_index)}(source_index)
        term(source_index) = fn(lambda_index Z) Z {term(lambda_index)}(source_index)
    by def $fn_eq(term, fn(lambda_index Z) Z {term(lambda_index)})
    term = fn(lambda_index Z) Z {term(lambda_index)}
    sum(first, last, term) = sum(first, last, fn(lambda_index Z) Z {term(lambda_index)})
    claim:
        ? forall shifted_index Z:
            first - 1 <= shifted_index
            shifted_index <= last - 1
            =>:
                term(shifted_index + 1) = term(shifted_index + 1)
        term(shifted_index + 1) = term(shifted_index + 1)
    sum(first, last, fn(lambda_index Z) Z {term(lambda_index)}) = sum(first + (-1), last + (-1), fn(shifted_index Z) Z {term(shifted_index + 1)})
    sum(first + (-1), last + (-1), fn(shifted_index Z) Z {term(shifted_index + 1)}) = sum(first - 1, last - 1, fn(shifted_index Z) Z {term(shifted_index + 1)})
    finite_integer_sum(first, last, term) = finite_integer_sum(first - 1, last - 1, fn(shifted_index Z) Z {term(shifted_index + 1)})
"#;

            let mut runtime = Runtime::default();
            runtime.start_isolated_source("committed_local_proofs_can_repeat_a_nested_binder_fact");
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                run_succeeded,
                "committed local proofs may repeat the same nested-binder proposition:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn stored_fact_lookup_still_rejects_a_different_proposition() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("stored_fact_lookup_still_rejects_a_different_proposition");
    let (stmt_results, runtime_error) = execute_source("1 = 1\n2 = 2\n", &mut runtime);
    assert!(runtime_error.is_none());

    let stored: Vec<(Fact, FactId)> = stmt_results
        .iter()
        .filter_map(|result| {
            let StmtResult::Success(SuccessStmtResult::Fact(result)) = result else {
                return None;
            };
            result
                .store
                .fact_id
                .map(|fact_id| (result.store.fact.clone(), fact_id))
        })
        .collect();
    assert_eq!(stored.len(), 2, "both facts should have stable identities");

    let mut store = EnvironmentStoredFactStore::default();
    store
        .record_fact(stored[0].0.clone(), stored[0].1)
        .expect("the first canonical fact should register");
    store
        .record_fact(stored[1].0.clone(), stored[1].1)
        .expect("the second canonical fact should register");

    let mut canonical_store = EnvironmentStoredFactStore::default();
    canonical_store
        .record_fact(stored[0].0.clone(), stored[0].1)
        .expect("the first canonical fact should register");
    let canonical_error = canonical_store
        .record_fact(stored[1].0.clone(), stored[0].1)
        .expect_err("one FactId must not identify a different proposition");
    let RuntimeError::StoreFactError(canonical_detail) = canonical_error else {
        panic!("canonical FactId retargeting should remain a StoreFactError");
    };
    assert!(
        canonical_detail.msg.contains("cannot retarget"),
        "{}",
        canonical_detail.msg
    );

    store
        .record_lookup_key(
            "shared-test-key".to_string(),
            default_line_file(),
            stored[0].1,
        )
        .expect("the first lookup should register");
    let error = store
        .record_lookup_key(
            "shared-test-key".to_string(),
            default_line_file(),
            stored[1].1,
        )
        .expect_err("a different proposition must not reuse the lookup key");
    let RuntimeError::StoreFactError(detail) = error else {
        panic!("lookup retargeting should remain a StoreFactError");
    };
    assert!(detail.msg.contains("cannot retarget"), "{}", detail.msg);
}

#[test]
fn one_fact_id_accepts_an_alpha_equivalent_nested_binder_spelling() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("one_fact_id_accepts_an_alpha_equivalent_nested_binder_spelling");
    let source_code = r#"
fn(alpha_index Z) Z {alpha_index}(1) $in Z
fn(beta_index Z) Z {beta_index}(1) $in Z
"#;
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    assert!(
        run_succeeded,
        "alpha-equivalent facts should verify:\n{run_output}"
    );

    let stored: Vec<(Fact, FactId)> = stmt_results
        .iter()
        .filter_map(|result| {
            let StmtResult::Success(SuccessStmtResult::Fact(result)) = result else {
                return None;
            };
            result
                .store
                .fact_id
                .map(|fact_id| (result.store.fact.clone(), fact_id))
        })
        .collect();
    assert_eq!(stored.len(), 2);
    assert_eq!(
        stored[0].1, stored[1].1,
        "alpha-equivalent lookup should reuse the original FactId"
    );

    let mut store = EnvironmentStoredFactStore::default();
    store
        .record_fact(stored[0].0.clone(), stored[0].1)
        .expect("the first spelling should register");
    store
        .record_fact(stored[1].0.clone(), stored[1].1)
        .expect("the alpha-equivalent spelling should preserve the FactId");
}

#[test]
fn run_isolated_file_from_path() {
    run_with_large_stack(
        "run_isolated_file_from_path_large_stack",
        run_isolated_file_from_path_impl,
    );
}

fn run_isolated_file_from_path_impl() {
    let path: String = "./examples/_internal/regression/enumerate_finite_set.lit".to_string();
    let file_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
    assert!(
        file_path.is_absolute(),
        "path must be an absolute path: {:?}",
        file_path
    );
    assert!(
        file_path.is_file(),
        "path must point to a file: {:?}",
        file_path
    );

    let source_code = match fs::read_to_string(&file_path) {
        Ok(content) => content,
        Err(read_error) => panic!("failed to read {:?}: {}", file_path, read_error),
    };
    let path_str = match file_path.to_str() {
        Some(path_string) => path_string,
        None => panic!("{:?} must be valid UTF-8", file_path),
    };

    let mut runtime = Runtime::default();
    runtime.start_isolated_source(path_str);
    let normalized_source = remove_windows_carriage_from_str(source_code.as_str());

    let start_time = Instant::now();
    let (stmt_results, runtime_error) = execute_source(normalized_source.as_str(), &mut runtime);
    let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    let status_label = if run_succeeded { "OK" } else { "FAILED" };
    println!(
        "{}\n=== [{}] {:?} ({:.2} ms user file only) ===\n",
        run_output, path_str, status_label, duration_ms
    );
    let error_json = match &runtime_error {
        Some(error) => render_runtime_error_json(&runtime, error, false),
        None => run_output.clone(),
    };
    assert!(
        run_succeeded,
        "Litex file failed: {}\n\n>>> Litex error JSON:\n{}\n\n=== [{}] {:?} ({:.2} ms user file only) ===",
        path_str, error_json, path_str, status_label, duration_ms
    );
}
