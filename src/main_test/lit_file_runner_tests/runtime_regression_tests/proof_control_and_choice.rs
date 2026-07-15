use super::*;

#[test]
fn sketch_stmt_is_checked_and_local() {
    let source_code = r#"
sketch:
    trust:
        2 = 3
2 = 3
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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
fn try_stmt_rejects_nested_control_statement() {
    run_with_large_stack("try_stmt_rejects_nested_control_statement", || {
        let source_code = r#"
try:
    sketch:
        clear
"#;

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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
            run_output.contains("try:") || run_output.contains("have a R"),
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
fn former_compatibility_words_are_ordinary_identifiers() {
    let source_code = r#"
have let set
have scratch set
have export set
have oo set
have oc set
have co set
have cc set
have oinf set
have cinf set
have info set
have infc set
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "former_compatibility_words_are_ordinary_identifiers",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "former compatibility words should be available as names:\n{run_output}"
    );
}

#[test]
fn internal_claim_question_goal_remains_supported() {
    run_with_large_stack("internal_claim_question_goal_remains_supported", || {
        let source_code = r#"
claim:
    ? 1 = 1
    1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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
    ? forall! n range(0, 3) => {n < 3}

by enumerate finite_set:
    ? forall! z {1, 2} => {z $in {1, 2}}

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

        let mut runtime = Runtime::new_with_builtin_code();
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
fn prove_is_available_as_an_identifier() {
    run_with_large_stack("prove_is_available_as_an_identifier", || {
        let source_code = r#"
prop prove(x R):
    x = x

$prove(1)
"#;
        let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
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
fn nested_forall_reusing_outer_param_is_rejected() {
    let source_code = r#"
forall x R:
    forall x R:
        x = x
    =>:
        x = x
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
        run_output.contains("free parameter `x` is already bound as Forall in an active scope")
            || run_output.contains("duplicate Forall free parameter `x` in nested scope"),
        "failure should mention duplicate forall parameter:\n{}",
        run_output
    );
}

#[test]
fn inline_by_for_and_enumerate_allow_empty_proof_without_trailing_colon() {
    let source_code = r#"
by for forall! n range(0, 3) => {n < 3}

by enumerate finite_set forall! x {1, 2} => {x $in {1, 2}}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "inline_by_for_and_enumerate_allow_empty_proof_without_trailing_colon",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "inline by-for/by-enumerate empty proof syntax failed:\n{}",
        run_output
    );
}

#[test]
fn by_enumerate_finite_set_resolves_named_literal_alias() {
    let source_code = r#"
have P finite_set = {1, 2}

by enumerate finite_set:
    ? forall x P:
        x = 1 or x = 2
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "by_enumerate_finite_set_resolves_named_literal_alias",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    assert!(
        run_succeeded,
        "finite-set enumeration over a named literal alias failed:\n{}",
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

            let mut runtime = Runtime::new_with_builtin_code();
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
            exist delta R_pos st {fn(x E) R {1 / g(x)} $in fn(x E) R}
    trust exist delta R_pos st {fn(x E) R {1 / g(x)} $in fn(x E) R}
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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
fn anonymous_quotient_lambda_over_punctured_set_is_well_defined() {
    run_with_large_stack(
        "anonymous_quotient_lambda_over_punctured_set_is_well_defined",
        || {
            let source_code = r#"
forall X power_set(R), x0 X:
    fn(x set_minus(X, {x0})) R {1 / (x - x0)} $in fn(x set_minus(X, {x0})) R
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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
fn by_zorn_lemma_stores_maximal_element_exist_fact() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)

by zorn_lemma: set s, prop leq:
    trust $is_nonempty_set(s)
    trust:
        forall x s:
            $leq(x, x)
        forall x, y, z s:
            $leq(x, y)
            $leq(y, z)
            =>:
                $leq(x, z)
        forall x, y s:
            $leq(x, y)
            $leq(y, x)
            =>:
                x = y
        forall C power_set(s):
            forall x, y C:
                $leq(x, y) or $leq(y, x)
            =>:
                exist u s st {forall! x C => {$leq(x, u)}}

exist m s st {forall! x s: $leq(m, x) => {x = m}}
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_stores_maximal_element_exist_fact",
    );

    assert!(
        run_succeeded,
        "by_zorn_lemma_stores_maximal_element_exist_fact failed:\n{}",
        run_output
    );
}

#[test]
fn by_zorn_lemma_without_trailing_colon_reaches_obligation_check() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)

by zorn_lemma: set s, prop leq
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_without_trailing_colon_reaches_obligation_check",
    );

    assert!(
        !run_succeeded,
        "missing zorn obligations should still fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("nonempty obligation"),
        "no-trailing-colon zorn syntax should reach obligation checking:\n{}",
        run_output
    );
}

#[test]
fn by_zorn_lemma_rejects_non_binary_prop() {
    let source_code = r#"
have s set
abstract_prop leq(x)

by zorn_lemma: set s, prop leq:
    trust $is_nonempty_set(s)
"#;

    let (run_succeeded, run_output) =
        run_zorn_lemma_regression_source(source_code, "by_zorn_lemma_rejects_non_binary_prop");

    assert!(
        !run_succeeded,
        "unary prop should make by zorn_lemma fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("must be a binary user-defined prop"),
        "failure should mention binary prop arity:\n{}",
        run_output
    );
}

#[test]
fn by_zorn_lemma_reports_missing_chain_upper_bound() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)

by zorn_lemma: set s, prop leq:
    trust $is_nonempty_set(s)
    trust:
        forall x s:
            $leq(x, x)
        forall x, y, z s:
            $leq(x, y)
            $leq(y, z)
            =>:
                $leq(x, z)
        forall x, y s:
            $leq(x, y)
            $leq(y, x)
            =>:
                x = y
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_reports_missing_chain_upper_bound",
    );

    assert!(
        !run_succeeded,
        "missing chain upper-bound should make by zorn_lemma fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("chain_upper_bound obligation"),
        "failure should name the missing chain upper-bound obligation:\n{}",
        run_output
    );
}

#[test]
fn by_zorn_lemma_failed_body_stmt_does_not_continue() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)

by zorn_lemma: set s, prop leq:
    1 = 2
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_failed_body_stmt_does_not_continue",
    );

    assert!(
        !run_succeeded,
        "failed body statement should make by zorn_lemma fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("failed to execute proof stmt"),
        "failure should mention the body statement:\n{}",
        run_output
    );
}

#[test]
fn by_zorn_lemma_rejects_old_from_syntax() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)

by zorn_lemma s from leq:
    trust $is_nonempty_set(s)
"#;

    let (run_succeeded, run_output) =
        run_zorn_lemma_regression_source(source_code, "by_zorn_lemma_rejects_old_from_syntax");

    assert!(
        !run_succeeded,
        "old by_zorn_lemma syntax should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("expected `by zorn_lemma: set S, prop P:`"),
        "failure should mention the new syntax:\n{}",
        run_output
    );
}

fn run_zorn_lemma_regression_source(source_code: &str, file_label: &str) -> (bool, String) {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(file_label);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false)
}

#[test]
fn by_axiom_of_choice_stores_choice_function_exist_fact() {
    let source_code = r#"
have S set

by axiom_of_choice: set S:
    trust forall A S:
        $is_nonempty_set(A)

exist f fn(A S) cup(S) st {forall! A S => {f(A) $in A}}
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_stores_choice_function_exist_fact",
    );

    assert!(
        run_succeeded,
        "by_axiom_of_choice_stores_choice_function_exist_fact failed:\n{}",
        run_output
    );
}

#[test]
fn by_axiom_of_choice_allows_empty_proof_without_trailing_colon() {
    let source_code = r#"
have S set
trust forall A S:
    $is_nonempty_set(A)

by axiom_of_choice: set S

exist f fn(A S) cup(S) st {forall! A S => {f(A) $in A}}
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_allows_empty_proof_without_trailing_colon",
    );

    assert!(
        run_succeeded,
        "by_axiom_of_choice_allows_empty_proof_without_trailing_colon failed:\n{}",
        run_output
    );
}

#[test]
fn by_axiom_of_choice_reports_missing_members_nonempty() {
    let source_code = r#"
have S set

by axiom_of_choice: set S:
    do_nothing
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_reports_missing_members_nonempty",
    );

    assert!(
        !run_succeeded,
        "missing members-nonempty obligation should make by axiom_of_choice fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("members_nonempty obligation"),
        "failure should name the missing members-nonempty obligation:\n{}",
        run_output
    );
}

#[test]
fn by_axiom_of_choice_failed_body_stmt_does_not_continue() {
    let source_code = r#"
have S set

by axiom_of_choice: set S:
    1 = 2
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_failed_body_stmt_does_not_continue",
    );

    assert!(
        !run_succeeded,
        "failed body statement should make by axiom_of_choice fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("failed to execute proof stmt"),
        "failure should mention the body statement:\n{}",
        run_output
    );
}

#[test]
fn by_axiom_of_choice_rejects_old_set_syntax() {
    let source_code = r#"
have S set

by axiom_of_choice S:
    trust forall A S:
        $is_nonempty_set(A)
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_rejects_old_set_syntax",
    );

    assert!(
        !run_succeeded,
        "old by_axiom_of_choice syntax should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("expected `by axiom_of_choice: set S:`"),
        "failure should mention the new syntax:\n{}",
        run_output
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
    let mut runtime = Runtime::new_with_builtin_code();
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
