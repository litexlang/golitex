use super::*;

#[test]
fn positive_real_power_closure_enables_log_inverse() {
    let source_code = r#"
forall a R_pos, x R:
    a^x $in R_pos

forall a R_pos, x, y R:
    a^x = y
    =>:
        y $in R_pos

forall a R_pos, x, y R:
    a != 1
    a^x = y
    =>:
        x = log(a, y)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("positive_real_power_closure_enables_log_inverse");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "positive_real_power_closure_enables_log_inverse failed:\n{}",
        run_output
    );
    assert!(run_output.contains("R_pos: a^x from 0 < a and x in R"));
    assert!(run_output.contains("equality: log(a, b) = c from a^c = b"));
}

#[test]
fn forall_iff_output_reports_direction_checks() {
    let source_code = r#"
forall a, b R_pos, c R:
    a != 1
    =>:
        log(a, b) = c
    <=>:
        a^c = b
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_iff_output_reports_direction_checks");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall_iff_output_reports_direction_checks failed:\n{}",
        run_output
    );
    assert!(run_output.contains("forall iff: then=>iff and iff=>then verified"));
    assert!(!run_output.contains("\"type\": \"cite forall iff fact\""));
}

#[test]
fn definition_namespaces_allow_same_spelling_across_kinds() {
    let source_code = r#"
have fn SharedName(x R) R = 1
algo SharedName(x):
    1
prop SharedName(x R)
struct SharedName:
    value R
    other R
template<s set>:
    have SharedName set = s
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "definition_namespaces_allow_same_spelling_across_kinds",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "same spelling across independent definition namespaces failed:\n{}",
        run_output
    );
}

#[test]
fn duplicate_definition_names_fail_in_their_namespace() {
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
            "algo",
            "have fn dup_algo(x R) R = 1\nalgo dup_algo(x):\n    1\nalgo dup_algo(x):\n    1",
        ),
        (
            "auto algo",
            "have fn as algo dup_auto_algo(x R) R = 1\nalgo dup_auto_algo(x):\n    1",
        ),
    ];

    for (label, source_code) in cases {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            format!("duplicate_definition_names_{}", label).as_str(),
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "duplicate {} definition should fail, but succeeded:\n{}",
            label, run_output
        );
        assert!(
            run_output.contains("NameAlreadyUsedError"),
            "duplicate {} definition should report NameAlreadyUsedError:\n{}",
            label,
            run_output
        );
    }
}

#[test]
fn alias_prop_copies_existing_prop_definition() {
    let source_code = r#"
prop is_one(x R):
    x = 1
alias prop one_prop <=> is_one
$one_prop(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("alias_prop_copies_existing_prop_definition");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "alias prop should copy and store the target prop definition:\n{}",
        run_output
    );
    assert!(runtime.get_prop_definition_by_name("one_prop").is_some());
}

#[test]
fn alias_thm_copies_existing_theorem_definition() {
    let source_code = r#"
thm one_eq_one:
    ? forall x R:
        x = 1
        =>:
            x = 1
alias thm same_one <=> one_eq_one
1 = 1
by thm same_one(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("alias_thm_copies_existing_theorem_definition");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "alias thm should copy and store the target theorem:\n{}",
        run_output
    );
    assert!(runtime.get_thm_definition_by_name("same_one").is_some());
}

#[test]
fn unicode_alias_prop_name_works() {
    run_with_large_stack("unicode_alias_prop_name_works", || {
        let source_code = r#"
prop is_one(x R):
    x = 1
alias prop 是一 <=> is_one
$是一(1)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("unicode_alias_prop_name_works");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "unicode alias prop names should work:\n{}",
            run_output
        );
        assert!(
            run_output.contains("alias prop 是一 <=> is_one"),
            "output should include the Chinese prop alias statement:\n{}",
            run_output
        );
        assert!(
            run_output.contains("$是一(1)"),
            "output should include use of the Chinese prop alias:\n{}",
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

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("unicode_object_name_works");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "unicode object names should work:\n{}",
            run_output
        );
    });
}

#[test]
fn unicode_alias_thm_name_works() {
    run_with_large_stack("unicode_alias_thm_name_works", || {
        let source_code = r#"
thm self_eq_en:
    ? forall x R:
        x = x
    x = x
alias thm 自反等式 <=> self_eq_en
by thm 自反等式(1)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("unicode_alias_thm_name_works");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "unicode alias theorem names should work:\n{}",
            run_output
        );
        assert!(
            run_output.contains("alias thm 自反等式 <=> self_eq_en"),
            "output should include the Chinese theorem alias statement:\n{}",
            run_output
        );
        assert!(
            run_output.contains("by thm 自反等式(1)"),
            "output should include use of the Chinese theorem alias:\n{}",
            run_output
        );
    });
}

#[test]
fn alias_prop_rejects_abstract_prop_target() {
    let source_code = r#"
abstract_prop abstract_target(x)
alias prop concrete_alias <=> abstract_target
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("alias_prop_rejects_abstract_prop_target");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "alias prop should reject abstract_prop targets:\n{}",
        run_output
    );
    assert!(
        run_output.contains("alias prop only supports concrete prop definitions"),
        "alias prop abstract target error should explain the restriction:\n{}",
        run_output
    );
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

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "thm_definition_stores_forall_fact_for_known_forall_use",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

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
fn thm_definition_can_still_be_used_by_thm() {
    run_with_large_stack("thm_definition_can_still_be_used_by_thm", || {
        let source_code = r#"
prop target_thm_prop(x R):
    x = 1

thm use_target_thm:
    ? forall x R:
        x = 1
        =>:
            $target_thm_prop(x)

    x = 1

by thm use_target_thm(1)
$target_thm_prop(1)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("thm_definition_can_still_be_used_by_thm");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "thm should remain available through explicit by thm calls:\n{}",
            run_output
        );
    });
}

#[test]
fn by_thm_releases_instantiated_then_facts() {
    run_with_large_stack("by_thm_releases_instantiated_then_facts", || {
        let source_code = r#"
abstract_prop target_thm_prop(x)

thm use_target_thm:
    ? forall x R:
        x = 1
        =>:
            $target_thm_prop(x)

    trust $target_thm_prop(x)

by thm use_target_thm(1)
$target_thm_prop(1)
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("by_thm_releases_instantiated_then_facts");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "explicit by thm should release the instantiated then-fact:\n{}",
            run_output
        );
    });
}

#[test]
fn strategy_definition_auto_enables_strategy() {
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

$target_strategy_prop(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strategy_definition_auto_enables_strategy");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "strategy definition should enable the strategy immediately:\n{}",
        run_output
    );

    let env = &runtime.current_module().main_environment;
    assert_eq!(
        env.used_strategy_stmts
            .get(&("target_strategy_prop".to_string(), true)),
        Some(&"use_target_strategy".to_string())
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

stop strategy use_target_strategy

claim:
    ? forall z R:
        z = 1
        =>:
            $target_strategy_prop(z)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "strategy_definition_stores_forall_fact_for_known_forall_use",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "strategy definition should store its proved forall for known-forall use:\n{}",
        run_output
    );
}

#[test]
fn strategy_definition_use_and_stop_are_stored() {
    let source_code = r#"
prop target_strategy_prop(x R):
    x = 1

strategy use_target_strategy:
    ? forall x R:
        x = 1
        =>:
            $target_strategy_prop(x)

use strategy use_target_strategy
stop strategy use_target_strategy
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strategy_definition_use_and_stop_are_stored");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "strategy definition/use/stop should succeed:\n{}",
        run_output
    );

    let env = &runtime.current_module().main_environment;
    assert!(env
        .defined_strategy_stmts
        .contains_key("use_target_strategy"));
    assert_eq!(
        env.used_strategy_stmts
            .get(&("target_strategy_prop".to_string(), true)),
        Some(&"use_target_strategy".to_string())
    );
    assert_eq!(
        env.stopped_strategy_stmts
            .get(&("target_strategy_prop".to_string(), true)),
        Some(&"use_target_strategy".to_string())
    );
}

#[test]
fn by_strategy_is_not_a_valid_by_subkeyword() {
    let source_code = r#"
prop target_strategy_prop(x R):
    x = 1

strategy use_target_strategy:
    ? forall x R:
        x = 1
        =>:
            $target_strategy_prop(x)

by strategy use_target_strategy
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("by_strategy_is_not_a_valid_by_subkeyword");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "`by strategy` should not parse as strategy activation:\n{}",
        run_output
    );
    assert!(
        run_output.contains("got `strategy`"),
        "the parser should report that strategy is not a valid `by` subkeyword:\n{}",
        run_output
    );
}

#[test]
fn strategy_positive_and_negative_atomic_keys_do_not_collide() {
    let source_code = r#"
abstract_prop target_strategy_prop(x)

strategy use_positive_strategy:
    ? forall x R:
        x = 1
        =>:
            $target_strategy_prop(x)

    trust:
        forall y R:
            y = 1
            =>:
                $target_strategy_prop(y)

strategy use_negative_strategy:
    ? forall x R:
        x != 1
        =>:
            not $target_strategy_prop(x)

    trust:
        forall y R:
            y != 1
            =>:
                not $target_strategy_prop(y)

use strategy use_positive_strategy
use strategy use_negative_strategy
stop strategy use_negative_strategy
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "strategy_positive_and_negative_atomic_keys_do_not_collide",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "positive and negative strategy keys should both be stored:\n{}",
        run_output
    );

    let env = &runtime.current_module().main_environment;
    assert_eq!(
        env.used_strategy_stmts
            .get(&("target_strategy_prop".to_string(), true)),
        Some(&"use_positive_strategy".to_string())
    );
    assert_eq!(
        env.used_strategy_stmts
            .get(&("target_strategy_prop".to_string(), false)),
        Some(&"use_negative_strategy".to_string())
    );
    assert_eq!(
        env.stopped_strategy_stmts
            .get(&("target_strategy_prop".to_string(), false)),
        Some(&"use_negative_strategy".to_string())
    );
    assert_eq!(
        env.stopped_strategy_stmts
            .get(&("target_strategy_prop".to_string(), true)),
        None
    );
}

#[test]
fn use_strategy_verifies_matching_atomic_fact_and_stop_leaves_known_forall_available() {
    let strategy_setup = r#"
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
"#;
    let succeeds_source_code = format!(
        "{}\nuse strategy use_target_strategy\n$target_strategy_prop(1)\n",
        strategy_setup
    );
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("use_strategy_verifies_matching_atomic_fact");
    let (stmt_results, runtime_error) =
        run_source_code(succeeds_source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "enabled strategy should verify the matching atomic fact:\n{}",
        run_output
    );

    let stop_source_code = format!(
        "{}\nuse strategy use_target_strategy\nstop strategy use_target_strategy\n$target_strategy_prop(1)\n",
        strategy_setup
    );
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("stop_strategy_leaves_known_forall_available");
    let (stmt_results, runtime_error) = run_source_code(stop_source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "stopped strategy search should still leave the stored forall available:\n{}",
        run_output
    );
    assert!(
        run_output.contains("cite forall fact"),
        "the stopped strategy case should verify by ordinary known-forall search:\n{}",
        run_output
    );
}

#[test]
fn use_strategy_after_stop_in_same_env_removes_stop() {
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

use strategy use_target_strategy
stop strategy use_target_strategy
use strategy use_target_strategy
$target_strategy_prop(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("use_strategy_after_stop_in_same_env_removes_stop");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "same-env use after stop should re-enable the strategy:\n{}",
        run_output
    );

    let env = &runtime.current_module().main_environment;
    assert_eq!(
        env.stopped_strategy_stmts
            .get(&("target_strategy_prop".to_string(), true)),
        None
    );
}

#[test]
fn child_env_use_strategy_overrides_parent_stop_without_removing_it() {
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

use strategy use_target_strategy
stop strategy use_target_strategy
claim:
    ? $target_strategy_prop(1)
    use strategy use_target_strategy
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "child_env_use_strategy_overrides_parent_stop_without_removing_it",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "child-env use should override the parent stop while inside the child env:\n{}",
        run_output
    );

    let env = &runtime.current_module().main_environment;
    assert_eq!(
        env.stopped_strategy_stmts
            .get(&("target_strategy_prop".to_string(), true)),
        Some(&"use_target_strategy".to_string())
    );
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
        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope(format!("strategy_rejects_{}", label).as_str());
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

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

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strategy_rejects_non_atomic_dom_fact");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

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

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strategy_rejects_equal_then_fact");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

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
fn have_fn_as_algo_rejects_non_atomic_case_condition() {
    let source_code = "\
have fn as algo bad_algo_case(x, y R) R by cases:
    case x = 0 and y = 0: 0";
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("have_fn_as_algo_non_atomic_case");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "non-atomic generated algo case should fail, but succeeded:\n{}",
        run_output
    );
    assert!(
        run_output.contains("generated algo case")
            && run_output.contains("currently require atomic case conditions"),
        "non-atomic generated algo case should report a targeted error:\n{}",
        run_output
    );
}

#[test]
fn run_isolated_file_from_path() {
    run_with_large_stack(
        "run_isolated_file_from_path_large_stack",
        run_isolated_file_from_path_impl,
    );
}

fn run_isolated_file_from_path_impl() {
    let path: String = "./examples/_internal/regression/do_nothing.lit".to_string();
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

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(path_str);
    let normalized_source = remove_windows_carriage_return(source_code.as_str());

    let start_time = Instant::now();
    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    let status_label = if run_succeeded { "OK" } else { "FAILED" };
    println!(
        "{}\n=== [{}] {:?} ({:.2} ms user file only) ===\n",
        run_output, path_str, status_label, duration_ms
    );
    let error_json = match &runtime_error {
        Some(error) => display_runtime_error_json(&runtime, error, false),
        None => run_output.clone(),
    };
    assert!(
        run_succeeded,
        "Litex file failed: {}\n\n>>> Litex error JSON:\n{}\n\n=== [{}] {:?} ({:.2} ms user file only) ===",
        path_str, error_json, path_str, status_label, duration_ms
    );
}
