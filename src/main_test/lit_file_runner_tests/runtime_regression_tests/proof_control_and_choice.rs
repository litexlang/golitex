use super::*;

#[test]
fn sketch_stmt_is_checked_and_local() {
    let source_code = r#"
sketch:
    trust:
        2 = 3
2 = 3
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("sketch_stmt_is_checked_and_local");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "facts from sketch should not leak into the outer environment:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"proof sketch\""),
        "sketch should be reported as proof sketch:\n{}",
        run_output
    );
    assert!(
        run_output.contains("sketch:\\n"),
        "sketch output should use the canonical `sketch:` spelling:\n{}",
        run_output
    );
}

#[test]
fn try_stmt_is_checked_and_committed() {
    run_with_large_stack("try_stmt_is_checked_and_committed", || {
        let source_code = r#"
try:
    have x R = 1
    x = 1
x = 1
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("try_stmt_is_checked_and_committed");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "try should commit successful facts:\n{}",
            run_output
        );
        assert!(
            run_output.contains("\"type\": \"try block\""),
            "try should be reported as a try block:\n{}",
            run_output
        );
        assert!(
            run_output.contains("try:\\n"),
            "try output should use the canonical `try:` spelling:\n{}",
            run_output
        );
    });
}

#[test]
fn try_stmt_commit_merges_child_equality_into_parent_equality_class() {
    run_with_large_stack(
        "try_stmt_commit_merges_child_equality_into_parent_equality_class",
        || {
            let source_code = r#"
have a R = 1
try:
    have b R = a
b = 1
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "try_stmt_commit_merges_child_equality_into_parent_equality_class",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "try commit should replay child equalities through parent equality storage:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn try_stmt_commit_reactivates_parent_stopped_strategy() {
    run_with_large_stack(
        "try_stmt_commit_reactivates_parent_stopped_strategy",
        || {
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
try:
    use strategy use_target_strategy
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "try_stmt_commit_reactivates_parent_stopped_strategy",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "try commit should succeed when reactivating a strategy:\n{}",
                run_output
            );

            let env = &runtime.current_module().main_environment;
            assert_eq!(
                env.used_strategy_stmts
                    .get(&("target_strategy_prop".to_string(), true)),
                Some(&"use_target_strategy".to_string())
            );
            assert_eq!(
                env.stopped_strategy_stmts
                    .get(&("target_strategy_prop".to_string(), true)),
                None
            );
        },
    );
}

#[test]
fn try_stmt_rejects_clear_control_statement() {
    run_with_large_stack("try_stmt_rejects_clear_control_statement", || {
        let source_code = r#"
have x R
try:
    clear
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("try_stmt_rejects_clear_control_statement");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "try with clear should be rejected:\n{}",
            run_output
        );
        assert!(
            run_output.contains("try cannot contain control statement `clear`"),
            "try with clear should explain that control statements are disallowed:\n{}",
            run_output
        );

        let (stmt_results_after, runtime_error_after) = run_source_code("x = x", &mut runtime);
        let (run_succeeded_after, run_output_after) = render_run_source_code_output(
            &runtime,
            &stmt_results_after,
            &runtime_error_after,
            false,
        );
        assert!(
            run_succeeded_after,
            "rejected try should not have executed clear:\n{}",
            run_output_after
        );
    });
}

#[test]
fn try_stmt_rejects_import_control_statement() {
    run_with_large_stack("try_stmt_rejects_import_control_statement", || {
        let source_code = r#"
try:
    import std basics
"#;

        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("try_stmt_rejects_import_control_statement");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "try with import should be rejected:\n{}",
            run_output
        );
        assert!(
            run_output.contains("try cannot contain control statement `import`"),
            "try with import should explain that control statements are disallowed:\n{}",
            run_output
        );
    });
}

#[test]
fn try_stmt_rejects_nested_control_statement() {
    run_with_large_stack("try_stmt_rejects_nested_control_statement", || {
        let source_code = r#"
try:
    sketch:
        clear
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("try_stmt_rejects_nested_control_statement");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "try with nested clear should be rejected:\n{}",
            run_output
        );
        assert!(
            run_output.contains("try cannot contain control statement `clear`"),
            "nested control statement should be rejected before execution:\n{}",
            run_output
        );
    });
}

#[test]
fn try_stmt_unknown_is_reported_and_local() {
    run_with_large_stack("try_stmt_unknown_is_reported_and_local", || {
        let source_code = r#"
try:
    trust:
        2 = 3
    4 = 5
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("try_stmt_unknown_is_reported_and_local");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "unknown try body should fail:\n{}",
            run_output
        );
        assert!(
            run_output.contains("UnknownError") || run_output.contains("try failed"),
            "try should report the unknown inner step:\n{}",
            run_output
        );

        let (stmt_results_after, runtime_error_after) = run_source_code("2 = 3", &mut runtime);
        let (run_succeeded_after, run_output_after) = render_run_source_code_output(
            &runtime,
            &stmt_results_after,
            &runtime_error_after,
            false,
        );
        assert!(
            !run_succeeded_after,
            "facts from a failed try should not leak:\n{}",
            run_output_after
        );
    });
}

#[test]
fn try_stmt_error_is_reported_and_local() {
    run_with_large_stack("try_stmt_error_is_reported_and_local", || {
        let source_code = r#"
try:
    have a R
    have a R
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("try_stmt_error_is_reported_and_local");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "error try body should fail:\n{}",
            run_output
        );
        assert!(
            run_output.contains("try:")
                || run_output.contains("have a R")
                || run_output.contains("name `a` is already active"),
            "try should report the failing inner statement:\n{}",
            run_output
        );

        let (stmt_results_after, runtime_error_after) = run_source_code("have a R", &mut runtime);
        let (run_succeeded_after, run_output_after) = render_run_source_code_output(
            &runtime,
            &stmt_results_after,
            &runtime_error_after,
            false,
        );
        assert!(
            run_succeeded_after,
            "definitions from a failed try should not leak:\n{}",
            run_output_after
        );
    });
}

#[test]
fn internal_claim_question_goal_remains_supported() {
    run_with_large_stack("internal_claim_question_goal_remains_supported", || {
        let source_code = r#"
claim:
    ? 1 = 1
    1 = 1
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("internal_claim_question_goal_remains_supported");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "internal claim question goal should still run:\n{}",
            run_output
        );
    });
}

#[test]
fn internal_claim_question_goal_allows_proof_body() {
    run_with_large_stack("internal_claim_question_goal_allows_proof_body", || {
        let source_code = r#"
claim:
    ? forall x R:
        x = 1
        =>:
            x = 1
    trust x = 1
"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("internal_claim_question_goal_allows_proof_body");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "claim question goal with a proof body should still run:\n{}",
            run_output
        );
    });
}

#[test]
fn question_goal_is_the_only_goal_syntax() {
    run_with_large_stack("question_goal_is_the_only_goal_syntax", || {
        let source_code = r#"
claim:
    ? 1 = 1
    1 = 1

thm qgoal_self_eq_thm:
    ? forall x R:
        x = x
    x = x

thm qgoal_self_eq_extra:
    ? forall x R:
        x = x
    x = x

have fn qgoal_identity by exist!:
    ? forall x R:
        exist! y R st {y = x}
    trust exist! y R st {y = x}
    exist! y R st {y = x}

abstract_prop qgoal_p(x)
trust forall x R:
    $qgoal_p(x)

strategy qgoal_strategy:
    ? forall x R:
        $qgoal_p(x)
    $qgoal_p(x)

by contra:
    ? 1 = 1
    1 != 1
    impossible 1 = 1

by cases:
    ? 1 = 1
    ? 2 = 2
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1

by extension:
    ? {1} = {1}

by for:
    ? forall n range(0, 3) => {n < 3}

by enumerate finite_set:
    ? forall z {1, 2} => {z $in {1, 2}}

prop qgoal_same_obj(x set, y set):
    x = y

by symmetric_prop:
    ? forall x, y set:
        $qgoal_same_obj(x, y)
        =>:
            $qgoal_same_obj(y, x)
    x = y
    y = x

abstract_prop qgoal_induc_p(a)
trust $qgoal_induc_p(0)
trust forall m N:
    $qgoal_induc_p(m)
    =>:
        $qgoal_induc_p(m + 1)

by induc n from 0:
    ? $qgoal_induc_p(n)
    ? from n = 0:
        $qgoal_induc_p(0)
    ? induc:
        $qgoal_induc_p(n)
        $qgoal_induc_p(n + 1)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("question_goal_is_the_only_goal_syntax");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "question goal shorthand fixture failed:\n{}",
            run_output
        );
        assert!(
            run_output.contains("? 1 = 1"),
            "Display output should canonicalize goal blocks to question syntax:\n{}",
            run_output
        );
        assert!(
            !run_output.contains("prove:"),
            "Display output must use question goals:\n{}",
            run_output
        );
    });
}

#[test]
fn by_cases_accepts_bodyless_closed_cases_and_rejects_unclosed_cases() {
    run_with_large_stack("by_cases_bodyless_cases", || {
        let positive_source = r#"
by cases:
    ? 1 = 1
    case 1 = 1
    case 1 != 1:
        impossible 1 = 1
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("bodyless_case_closed");
        let (stmt_results, runtime_error) = run_source_code(positive_source, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert!(
            run_succeeded,
            "a bodyless case should succeed when its assumption closes the goal:\n{}",
            run_output
        );
        assert!(
            run_output.contains("case 1 = 1\\n"),
            "bodyless case output should omit the proof-body colon:\n{}",
            run_output
        );

        let negative_source = r#"
by cases:
    ? 1 = 2
    case 1 = 1
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("bodyless_case_unclosed");
        let (stmt_results, runtime_error) = run_source_code(negative_source, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert!(
            !run_succeeded,
            "a bodyless case must not bypass the final goal check:\n{}",
            run_output
        );
        assert!(
            run_output.contains("by cases: failed to prove `1 = 2` under case `1 = 1`"),
            "the failure should identify the unclosed goal and active case:\n{}",
            run_output
        );
    });
}

#[test]
fn bodyless_by_goal_blocks_still_close_targets_and_contra_requires_impossible() {
    run_with_large_stack("bodyless_by_goal_blocks", || {
        let selected_theorem_source = r#"
thm bodyless_zero_sides:
    ? forall x R:
        x + 0 = x
        0 + x = x

    x + 0 = x
    0 + x = x

by thm bodyless_zero_sides(2):
    ? 2 + 0 = 0 + 2

by induc n from 0:
    ? n = n

by strong_induc m from 0:
    ? m = m
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("bodyless_by_thm_goal_closed");
        let (results, error) = run_source_code(selected_theorem_source, &mut runtime);
        let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
        assert!(
            succeeded,
            "a bodyless by-thm goal should use the selected-fact verifier:\n{output}"
        );
        assert!(
            output.contains("by thm bodyless_zero_sides(2) => 2 + 0 = 0 + 2"),
            "bodyless by-thm output should retain the selected atomic target:\n{output}"
        );
        assert!(
            output.contains("by induc n from 0:\\n    ? n = n\"")
                && output.contains("by strong_induc m from 0:\\n    ? m = m\""),
            "bodyless induction output should not add a blank proof line:\n{output}"
        );

        let negative_cases = [
            (
                "by extension:\n    ? {1} = {2}",
                "by extension: failed to prove",
            ),
            (
                "by contra:\n    ? 1 = 1",
                "by contra: expects a `? <fact>` goal block and impossible ... tail",
            ),
        ];

        for (index, (source, expected)) in negative_cases.iter().enumerate() {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(&format!(
                "bodyless_by_goal_negative_{index}"
            ));
            let (results, error) = run_source_code(source, &mut runtime);
            let (succeeded, output) =
                render_run_source_code_output(&runtime, &results, &error, false);
            assert!(
                !succeeded,
                "an empty proof must not admit an unclosed target: {source}"
            );
            assert!(
                output.contains(expected),
                "missing bodyless-goal boundary diagnostic for {source:?}:\n{output}"
            );
        }
    });
}

#[test]
fn prove_is_available_as_an_identifier() {
    run_with_large_stack("prove_is_available_as_an_identifier", || {
        let source_code = r#"
prop prove(x R):
    x = x

$prove(1)
"#;
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("prove_is_available_as_an_identifier");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
        assert!(
            run_succeeded,
            "prove should be an ordinary identifier:\n{run_output}"
        );
    });
}

#[test]
fn top_level_question_goal_is_rejected_with_goal_block_hint() {
    run_with_large_stack(
        "top_level_question_goal_is_rejected_with_goal_block_hint",
        || {
            let source_code = r#"
? 1 = 1
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("top_level_question_goal_is_rejected");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "top-level question goal should be rejected:\n{}",
                run_output
            );
            assert!(
                run_output.contains("top-level `?` is not supported"),
                "top-level question goal should explain supported usage:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn fn_range_intro_subset_and_preimage_work() {
    run_with_large_stack("fn_range_intro_subset_and_preimage_work", || {
        let source_code = r#"
sketch:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    fn_range(f) $subset R
    fn_range(f) $in power_set(R)

    have by preimage x from f(1) $in fn_range(f)
    x $in R
    x > 0
    f(1) = f(x)

sketch:
    have g fn(x R, y R: x < y) R

    g(0, 1) $in fn_range(g)

    have by preimage a, b from g(0, 1) $in fn_range(g)
    a $in R
    b $in R
    a < b
    g(0, 1) = g(a, b)

sketch:
    have a seq(R)

    fn(x 1...3) R {a(x)}(1) $in fn_range(fn(x 1...3) R {a(x)})
    fn(x 1...3) R {a(x)}(2) $in fn_range(fn(x 1...3) R {a(x)})
    fn_range(fn(x 1...3) R {a(x)}) $subset R
    fn_range(fn(x 1...3) R {a(x)}) $in power_set(R)
    $is_finite_set(fn_range(fn(x 1...3) R {a(x)}))
    finite_set_size(fn_range(fn(x 1...3) R {a(x)})) $in N

    have by preimage k from fn(x 1...3) R {a(x)}(2) $in fn_range(fn(x 1...3) R {a(x)})
    k $in 1...3
    fn(x 1...3) R {a(x)}(2) = fn(x 1...3) R {a(x)}(k)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("fn_range_intro_subset_and_preimage_work");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "fn_range intro/subset/preimage failed:\n{}",
            run_output
        );
    });
}

#[test]
fn fn_range_membership_infers_preimage_existence() {
    run_with_large_stack("fn_range_membership_infers_preimage_existence", || {
        let source_code = r#"
have f fn(x R) R

claim:
    ? forall y fn_range(f):
        exist x R st {y = f(x)}
    exist x R st {y = f(x)}

claim:
    ? forall y fn_range(f):
        exist x R st {y = f(x)}
    y $in fn_range(f)
    exist x R st {y = f(x)}

"#;

        let mut runtime = Runtime::new();
        runtime
            .new_file_path_new_env_new_name_scope("fn_range_membership_infers_preimage_existence");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "fn_range membership should infer preimage existence:\n{}",
            run_output
        );
    });
}

#[test]
fn have_by_preimage_rejects_non_range_source() {
    run_with_large_stack("have_by_preimage_rejects_non_range_source", || {
        let source_code = r#"
sketch:
    have f fn(x R) R
    have by preimage x from f(1) $in R
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("have_by_preimage_rejects_non_range_source");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "preimage with non-range source should fail:\n{}",
            run_output
        );
        assert!(
            run_output.contains("have by preimage expects `from z $in fn_range(f)`"),
            "preimage non-range error should be explicit:\n{}",
            run_output
        );
    });
}

#[test]
fn have_by_preimage_checks_witness_count() {
    run_with_large_stack("have_by_preimage_checks_witness_count", || {
        let source_code = r#"
sketch:
    have f fn(x R) R
    f(1) $in fn_range(f)
    have by preimage x, y from f(1) $in fn_range(f)
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("have_by_preimage_checks_witness_count");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "preimage witness count mismatch should fail:\n{}",
            run_output
        );
        assert!(
            run_output.contains("have by preimage: expected 1 preimage name(s), got 2"),
            "preimage witness count error should be explicit:\n{}",
            run_output
        );
    });
}

#[test]
fn replacement_requires_binary_prop() {
    run_with_large_stack("replacement_requires_binary_prop", || {
        let source_code = r#"
abstract_prop one_arg_relation(x)
have B set = replacement(one_arg_relation, {1})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("replacement_requires_binary_prop");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "unary replacement relation should fail:\n{}",
            run_output
        );
        assert!(
            run_output.contains("expects a binary prop"),
            "replacement arity error should be explicit:\n{}",
            run_output
        );
    });
}

#[test]
fn replacement_requires_uniqueness_over_source_set() {
    run_with_large_stack("replacement_requires_uniqueness_over_source_set", || {
        let source_code = r#"
abstract_prop rel(x, y)
have B set = replacement(rel, {1})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "replacement_requires_uniqueness_over_source_set",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            !run_succeeded,
            "replacement without uniqueness should fail:\n{}",
            run_output
        );
        assert!(
            run_output.contains("needs uniqueness of `rel` over `{1}`"),
            "replacement uniqueness error should be explicit:\n{}",
            run_output
        );
    });
}

#[test]
fn replacement_membership_infers_preimage_and_preimage_stmt_works() {
    run_with_large_stack(
        "replacement_membership_infers_preimage_and_preimage_stmt_works",
        || {
            let source_code = r#"
abstract_prop rel(x, y)

trust forall x {3, 5, 9}, y, y2 set:
    $rel(x, y)
    $rel(x, y2)
    =>:
        y = y2

have B set = replacement(rel, {3, 5, 9})

forall y B:
    exist x {3, 5, 9} st {$rel(x, y)}

have y set
trust y $in replacement(rel, {3, 5, 9})
have by preimage x from y $in replacement(rel, {3, 5, 9})
x $in {3, 5, 9}
$rel(x, y)
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "replacement_membership_infers_preimage_and_preimage_stmt_works",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "replacement membership/preimage should work:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn replacement_membership_intro_from_relation_witness() {
    run_with_large_stack("replacement_membership_intro_from_relation_witness", || {
        let source_code = r#"
abstract_prop rel(x, y)

trust forall x {1, 2}, y, y2 set:
    $rel(x, y)
    $rel(x, y2)
    =>:
        y = y2

have y set
trust $rel(1, y)

y $in replacement(rel, {1, 2})
"#;

        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(
            "replacement_membership_intro_from_relation_witness",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "replacement membership intro should work:\n{}",
            run_output
        );
        assert!(
            run_output
                .contains("replacement membership: a relation witness is in the replacement set"),
            "replacement membership intro rule should appear in verifier output:\n{}",
            run_output
        );
    });
}

#[test]
fn replacement_uniqueness_keeps_outer_same_spelling_parameter_rigid() {
    run_with_large_stack(
        "replacement_uniqueness_keeps_outer_same_spelling_parameter_rigid",
        || {
            let source_code = r#"
abstract_prop rel(a, y)

claim:
    ? forall x set:
        forall a {x}, y, y2 set:
            $rel(a, y)
            $rel(a, y2)
            =>:
                y = y2
        =>:
            replacement(rel, {x}) = replacement(rel, {x})
    forall a {x}, y, y2 set:
        $rel(a, y)
        $rel(a, y2)
        =>:
            y = y2
    replacement(rel, {x}) = replacement(rel, {x})
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "replacement_uniqueness_keeps_outer_same_spelling_parameter_rigid",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "replacement uniqueness must not capture the outer `x` in the source set:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn nested_forall_reusing_outer_param_is_rejected() {
    let source_code = r#"
forall x R:
    forall x R:
        x = x
    =>:
        x = x
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("nested_forall_reusing_outer_param_is_rejected");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "nested forall with duplicate param should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("name `x` is already active in this scope"),
        "failure should mention duplicate forall parameter:\n{}",
        run_output
    );
}

#[test]
fn induction_proof_local_names_do_not_leak_outside_their_proof_block() {
    let source_code = r#"
abstract_prop p(a)
trust $p(0)
trust forall m N:
    $p(m)
    =>:
        $p(m + 1)

by induc n from 0:
    ? $p(n)

    ? from n = 0:
        have x N = 0
        $p(0)

    ? induc:
        have y N = n
        $p(n + 1)

trust exist x R st {x = x}
trust exist y R st {y = y}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "induction_proof_local_names_do_not_leak_outside_their_proof_block",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "induction proof locals must be released after their branch:\n{}",
        run_output
    );
}

#[test]
fn parser_scope_rejects_active_cross_kind_reuse_and_releases_finished_scopes() {
    let invalid_source_code = r#"
trust:
    forall x R:
        exist x R st {x = x}
"#;

    let mut invalid_runtime = Runtime::new();
    invalid_runtime
        .new_file_path_new_env_new_name_scope("parser_scope_rejects_active_cross_kind_reuse");
    let (invalid_results, invalid_error) =
        run_source_code(invalid_source_code, &mut invalid_runtime);
    let (invalid_succeeded, invalid_output) =
        render_run_source_code_output(&invalid_runtime, &invalid_results, &invalid_error, false);
    assert!(
        !invalid_succeeded,
        "different binder kinds must not reuse an active spelling:\n{}",
        invalid_output
    );
    assert!(
        invalid_output.contains("name `x` is already active in this scope"),
        "the parser should identify the active-name collision:\n{}",
        invalid_output
    );

    let valid_source_code = r#"
trust forall x R:
    x = x

trust forall x R:
    x = x
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("parser_scope_releases_finished_scopes");
    let (stmt_results, runtime_error) = run_source_code(valid_source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "completed sibling scopes must release their spelling:\n{}",
        run_output
    );
}

#[test]
fn failed_scope_begin_does_not_leak_a_partial_binding() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("failed_scope_begin_does_not_leak");

    let (_, first_error) = run_source_code("trust have x, x R", &mut runtime);
    assert!(
        first_error.is_some(),
        "the duplicate binding must be rejected"
    );

    let (stmt_results, runtime_error) = run_source_code("trust have x R", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "a failed scope begin must not leave a partial binding:\n{}",
        run_output
    );
}

#[test]
fn failed_statement_parse_rolls_back_all_new_bindings() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("failed_statement_parse_rolls_back_bindings");

    let (_, first_error) = run_source_code("trust have x R, y", &mut runtime);
    assert!(
        first_error.is_some(),
        "the incomplete declaration must fail"
    );

    let (stmt_results, runtime_error) = run_source_code("trust have x R", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "a failed statement parse must roll back every new binding:\n{}",
        run_output
    );
}

#[test]
fn trust_statements_are_atomic() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("trust_statements_are_atomic");

    let failed_source = r#"
trust:
    777 = 778
    1 / 0 = 0
"#;
    let (failed_results, failed_error) = run_source_code(failed_source, &mut runtime);
    assert!(failed_results.is_empty());
    assert!(failed_error.is_some(), "the ill-defined fact must fail");
    assert!(
        !runtime.cache_known_facts_contains("777 = 778").0,
        "a failed trust statement must not retain its valid prefix"
    );

    let failed_summary =
        display_run_summary_json_with_runtime(&runtime, &failed_results, &failed_error);
    assert!(failed_summary.contains("\"direct_trust\": 0"));
    assert!(failed_summary.contains("\"known_facts\": 0"));

    let successful_source = r#"
trust:
    777 = 778
    888 = 889
"#;
    let (successful_results, successful_error) = run_source_code(successful_source, &mut runtime);
    assert!(successful_error.is_none());
    assert_eq!(successful_results.len(), 1);
    assert!(runtime.cache_known_facts_contains("777 = 778").0);
    assert!(runtime.cache_known_facts_contains("888 = 889").0);

    let later_failure = r#"
trust:
    999 = 1000
    1 / 0 = 0
"#;
    let (_, later_error) = run_source_code(later_failure, &mut runtime);
    assert!(later_error.is_some());
    assert!(
        runtime.cache_known_facts_contains("777 = 778").0,
        "a later failed statement must not roll back an earlier successful statement"
    );
    assert!(!runtime.cache_known_facts_contains("999 = 1000").0);
}

#[test]
fn trust_have_statements_are_atomic() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("trust_have_statements_are_atomic");

    let failed_source = r#"
trust have rollback_probe R:
    rollback_probe = rollback_probe
    1 / 0 = 0
"#;
    let (failed_results, failed_error) = run_source_code(failed_source, &mut runtime);
    assert!(failed_results.is_empty());
    assert!(
        failed_error.is_some(),
        "the ill-defined attached fact must fail"
    );
    assert!(
        !runtime.is_name_used_for_identifier("rollback_probe"),
        "a failed trust have statement must not retain its object binding"
    );
    assert!(
        !runtime
            .cache_known_facts_contains("rollback_probe = rollback_probe")
            .0
    );

    let (retry_results, retry_error) = run_source_code("trust have rollback_probe R", &mut runtime);
    let (retry_succeeded, retry_output) =
        render_run_source_code_output(&runtime, &retry_results, &retry_error, false);
    assert!(
        retry_succeeded,
        "the rolled-back name must be reusable immediately:\n{}",
        retry_output
    );

    let mut dependent_runtime = Runtime::new();
    dependent_runtime.new_file_path_new_env_new_name_scope("trust_have_keeps_local_prefix_visible");
    let dependent_source = r#"
trust have denominator R:
    denominator != 0
    1 / denominator = 1 / denominator
"#;
    let (dependent_results, dependent_error) =
        run_source_code(dependent_source, &mut dependent_runtime);
    let (dependent_succeeded, dependent_output) = render_run_source_code_output(
        &dependent_runtime,
        &dependent_results,
        &dependent_error,
        false,
    );
    assert!(
        dependent_succeeded,
        "later facts must see earlier facts inside the transaction:\n{}",
        dependent_output
    );

    let committed_probe = r#"
denominator != 0
2 / denominator = 2 / denominator
"#;
    let (probe_results, probe_error) = run_source_code(committed_probe, &mut dependent_runtime);
    let (probe_succeeded, probe_output) =
        render_run_source_code_output(&dependent_runtime, &probe_results, &probe_error, false);
    assert!(
        probe_succeeded,
        "the complete trust have transaction must be reusable afterward:\n{}",
        probe_output
    );
}

#[test]
fn inline_by_extension_for_and_enumerate_match_block_forms() {
    let source_code = r#"
by extension {1} = {1}

by extension:
    ? {2} = {2}

by for forall n range(0, 3) => {n < 3}

by for:
    ? forall m closed_range(0, 2) => {m <= 2}

by enumerate finite_set forall x {1, 2} => {x $in {1, 2}}

by enumerate finite_set:
    ? forall y {3, 4}:
        y = 3 or y = 4
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "inline_by_extension_for_and_enumerate_match_block_forms",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "inline and block proof-method goal forms should use the same executors:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"proof by extension\"")
            && run_output.contains("\"type\": \"proof by finite set enumeration\"")
            && run_output.contains("\"type\": \"proof by universal introduction\""),
        "all three inline forms should retain their existing proof provenance:\n{}",
        run_output
    );
}

#[test]
fn inline_by_proof_methods_keep_body_and_target_shape_boundaries() {
    let body_cases = [
        "by extension {1} = {1}:\n    do_nothing",
        "by for forall n range(0, 1) => {n < 1}:\n    do_nothing",
        "by enumerate finite_set forall n {0} => {n = 0}:\n    do_nothing",
    ];

    for (index, source_code) in body_cases.iter().enumerate() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(&format!("inline_by_body_{}", index));
        let (results, error) = run_source_code(source_code, &mut runtime);
        let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
        assert!(
            !succeeded,
            "an inline proof method must not accept an indented body: {source_code}"
        );
        assert!(
            output.contains("does not accept an indented body"),
            "the diagnostic should direct bodyful proofs to block form:\n{output}"
        );
    }

    let target_cases = [
        ("by extension 1 < 2", "goal expects equal fact"),
        ("by for 1 = 1", "expects a single forall fact"),
        (
            "by enumerate finite_set 1 = 1",
            "expects a single forall fact",
        ),
    ];

    for (index, (source_code, expected)) in target_cases.iter().enumerate() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(&format!("inline_by_target_{}", index));
        let (results, error) = run_source_code(source_code, &mut runtime);
        let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
        assert!(
            !succeeded,
            "an inline proof method must retain its target shape: {source_code}"
        );
        assert!(
            output.contains(expected),
            "the diagnostic should identify the required target shape:\n{output}"
        );
    }
}

#[test]
fn by_enumerate_finite_set_resolves_named_literal_definition() {
    let source_code = r#"
have P finite_set = {1, 2}

by enumerate finite_set:
    ? forall x P:
        x = 1 or x = 2
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "by_enumerate_finite_set_resolves_named_literal_definition",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "finite-set enumeration over a named literal definition failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"parameter_sets\": [") && run_output.contains("\"{1, 2}\""),
        "enumeration output should show the resolved displayed set:\n{}",
        run_output
    );
}

#[test]
fn anonymous_quotient_lambda_uses_nonzero_on_predicate() {
    run_with_large_stack(
        "anonymous_quotient_lambda_uses_nonzero_on_predicate",
        || {
            let source_code = r#"
prop nonzero_on(I power_set(R), g fn(x I) R):
    forall x I:
        g(x) != 0

forall I power_set(R), f, g fn(x I) R:
    $nonzero_on(I, g)
    =>:
        fn(x I) R {f(x) / g(x)} $in fn(x I) R
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_quotient_lambda_uses_nonzero_on_predicate",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "anonymous quotient lambda should inherit nonzero-on facts:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_quotient_lambda_without_nonzero_premise_is_rejected() {
    let source_code = r#"
forall E power_set(R), f, g fn(x E) R:
    fn(x E) R {f(x) / g(x)} $in fn(x E) R
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "anonymous_quotient_lambda_without_nonzero_premise_is_rejected",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "an anonymous quotient lambda without a nonzero premise must remain ill-defined"
    );
    assert!(
        run_output.contains("must be non-zero"),
        "the rejection should identify the missing divisor obligation:\n{}",
        run_output
    );
}

#[test]
fn anonymous_quotient_lambda_in_existential_respects_nonzero_on_predicate() {
    run_with_large_stack(
        "anonymous_quotient_lambda_in_existential_respects_nonzero_on_predicate",
        || {
            let source_code = r#"
prop nonzero_on(E power_set(R), g fn(x E) R):
    forall x E:
        g(x) != 0

thm nested_existential_quotient_is_well_defined:
    ? forall E power_set(R), g fn(x E) R:
        $nonzero_on(E, g)
        =>:
            exist delta R+ st {fn(x E) R {1 / g(x)} $in fn(x E) R}
    trust exist delta R+ st {fn(x E) R {1 / g(x)} $in fn(x E) R}
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_quotient_lambda_in_existential_respects_nonzero_on_predicate",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "anonymous quotient lambda in an existential should inherit nonzero-on facts:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn existential_well_definedness_uses_preceding_predicate_definition() {
    let source_code = r#"
prop nonzero(value R):
    value != 0

trust exist denominator R st {$nonzero(denominator), 1 / denominator = 1 / denominator}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "existential_well_definedness_uses_preceding_predicate_definition",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "a checked existential body should expose definition consequences to later facts:\n{}",
        run_output
    );
}

#[test]
fn existential_well_definedness_still_requires_a_nonzero_premise() {
    let source_code = r#"
trust exist denominator R st {1 / denominator = 1 / denominator}
"#;

    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(
        "existential_well_definedness_still_requires_a_nonzero_premise",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        !run_succeeded,
        "division without a preceding nonzero premise must remain ill-defined"
    );
    assert!(
        run_output.contains("must be non-zero"),
        "the rejection should identify the missing divisor obligation:\n{}",
        run_output
    );
}

#[test]
fn anonymous_quotient_lambda_over_punctured_set_is_well_defined() {
    run_with_large_stack(
        "anonymous_quotient_lambda_over_punctured_set_is_well_defined",
        || {
            let source_code = r#"
forall X power_set(R), x0 X:
    fn(x set_minus(X, {x0})) R {1 / (x - x0)} $in fn(x set_minus(X, {x0})) R
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "anonymous_quotient_lambda_over_punctured_set_is_well_defined",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
            assert!(
                run_succeeded,
                "anonymous quotient lambda over a punctured set should be well-defined:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_zorn_lemma_requires_a_named_property_result_interface() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)
by zorn_lemma: set s, prop leq
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_zorn_lemma_requires_a_named_property_result_interface",
    );
    assert!(
        !run_succeeded,
        "the legacy Zorn interface must fail:\n{run_output}"
    );
    assert!(
        run_output.contains(
            "by zorn_lemma is unavailable: its former conclusion used an anonymous `forall`"
        ),
        "the migration diagnostic should explain the named-property boundary:\n{run_output}"
    );
}

#[test]
fn by_axiom_of_choice_requires_the_general_cart_theorem_interface() {
    let source_code = r#"
have S set
by axiom_of_choice: set S
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_requires_the_general_cart_theorem_interface",
    );
    assert!(
        !run_succeeded,
        "the legacy choice interface must fail:\n{run_output}"
    );
    assert!(
        run_output.contains("use the explicit `general_cart_nonempty_by_choice_*` theorem"),
        "the migration diagnostic should name the replacement theorem:\n{run_output}"
    );
}

#[test]
fn choose_object_is_no_longer_builtin() {
    let source_code = r#"
trust have s nonempty_set:
    forall x s:
        $is_nonempty_set(x)

choose(s) $in s
"#;

    let (run_succeeded, run_output) =
        run_axiom_of_choice_regression_source(source_code, "choose_object_is_no_longer_builtin");

    assert!(
        !run_succeeded,
        "old choose(s) builtin object should no longer verify:\n{}",
        run_output
    );
    assert!(
        run_output.contains("choose"),
        "failure should still point at the old choose expression:\n{}",
        run_output
    );
}

fn run_axiom_of_choice_regression_source(source_code: &str, file_label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(file_label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}

#[test]
fn by_regularity_axiom_stores_foundation_witness_exist_fact() {
    run_with_large_stack(
        "by_regularity_axiom_stores_foundation_witness_exist_fact",
        || {
            let source_code = r#"
trust $is_nonempty_set({1, 2})

by regularity_axiom({1, 2})

exist x {1, 2} st {intersect(x, {1, 2}) = {}}
"#;

            let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
                source_code,
                "by_regularity_axiom_stores_foundation_witness_exist_fact",
            );

            assert!(
                run_succeeded,
                "by_regularity_axiom_stores_foundation_witness_exist_fact failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"by regularity_axiom proof\""),
                "success output should identify the regularity axiom step:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_regularity_axiom_requires_nonempty_set() {
    run_with_large_stack("by_regularity_axiom_requires_nonempty_set", || {
        let source_code = r#"
by regularity_axiom({})
"#;

        let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
            source_code,
            "by_regularity_axiom_requires_nonempty_set",
        );

        assert!(
            !run_succeeded,
            "empty set should not satisfy by regularity_axiom:\n{}",
            run_output
        );
        assert!(
            run_output.contains("nonempty obligation"),
            "failure should name the missing nonempty obligation:\n{}",
            run_output
        );
    });
}

#[test]
fn remaining_by_goal_header_shorthands_are_rejected() {
    let cases = [
        "by cases 1 = 1:\n    case 1 = 1:\n        do_nothing",
        "by contra 1 = 1:\n    impossible 1 != 1",
    ];

    for (index, source_code) in cases.iter().enumerate() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(&format!("removed_by_header_{}", index));
        let (results, error) = run_source_code(source_code, &mut runtime);
        let (succeeded, output) = render_run_source_code_output(&runtime, &results, &error, false);
        assert!(
            !succeeded,
            "removed by-goal header syntax unexpectedly passed: {source_code}"
        );
        assert!(
            output.contains("no longer accepts a goal on the header"),
            "missing migration diagnostic for {source_code:?}:\n{output}"
        );
    }
}
