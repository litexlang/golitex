use super::*;
use crate::parsing::Tokenizer;
use crate::test_support::execute_source;
use std::rc::Rc;

fn parse_fact_for_wd(runtime: &mut Runtime, source: &str, label: &str) -> Fact {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, Rc::from(label))
        .expect("WD fact fixture should tokenize");
    runtime
        .parse_fact(&mut blocks[0])
        .expect("WD fact fixture should parse")
}

fn try_execution(stmt_results: &[StmtResult]) -> &TryStmtExecutionResult {
    let [StmtResult::Success(SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::TryStmt(
        result,
    )))] = stmt_results
    else {
        panic!("expected one successful try statement result")
    };
    &result.execution
}

#[test]
fn example_stmt_is_checked_and_does_not_export_its_goal() {
    let source_code = r#"
have example_value R
example:
    ? example_value = 1
    trust:
        example_value = 1
example_value = 1
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("example_stmt_is_checked_and_does_not_export_its_goal");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "an example target must not leak into the outer environment:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"kind\": \"ExampleStmt\""),
        "example should retain its distinct public result kind:\n{}",
        run_output
    );
    assert!(
        run_output.contains("example:\\n"),
        "example output should use the canonical `example:` spelling:\n{}",
        run_output
    );
}

#[test]
fn example_stmt_accepts_a_checked_goal_without_exporting_bindings() {
    let source_code = r#"
example:
    ? forall local_value R:
        local_value = local_value
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("example_stmt_accepts_a_checked_goal_without_exporting_bindings");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(run_succeeded, "{run_output}");
    assert_eq!(stmt_results.len(), 1, "{run_output}");
    let StmtResult::Success(SuccessStmtResult::ProofBlock(
        SuccessProofBlockStmtResult::ExampleStmt(result),
    )) = &stmt_results[0]
    else {
        panic!("example should retain its exact verified IR: {run_output}")
    };
    assert!(
        result.common.infers.store_fact_outputs.is_empty(),
        "{run_output}"
    );
    assert!(result.verification.is_some(), "{run_output}");
}

#[test]
fn sketch_stmt_is_checked_and_local() {
    let source_code = r#"
sketch:
    trust:
        2 = 3
2 = 3
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("sketch_stmt_is_checked_and_local");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        !run_succeeded,
        "facts from sketch should not leak into the outer environment:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"kind\": \"SketchStmt\""),
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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("try_stmt_is_checked_and_committed");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "try should commit successful facts:\n{}",
            run_output
        );
        assert!(
            run_output.contains("\"kind\": \"TryStmt\""),
            "try should be reported as a try block:\n{}",
            run_output
        );
        assert!(
            run_output.contains("\"kind\": \"Committed\""),
            "try should report its committed transaction:\n{}",
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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "try_stmt_commit_merges_child_equality_into_parent_equality_class",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

            assert!(
                run_succeeded,
                "try commit should replay child equalities through parent equality storage:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn try_stmt_rejects_import_control_statement() {
    run_with_large_stack("try_stmt_rejects_import_control_statement", || {
        let source_code = r#"
try:
    import std basics
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("try_stmt_rejects_import_control_statement");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            !run_succeeded,
            "try with import should be rejected:\n{}",
            run_output
        );
        assert!(
            run_output.contains("`import` is a terminal command, not a Litex statement"),
            "try with import should explain the source/terminal boundary:\n{}",
            run_output
        );
    });
}

#[test]
fn try_stmt_unknown_rolls_back_and_returns_success() {
    run_with_large_stack("try_stmt_unknown_rolls_back_and_returns_success", || {
        let source_code = r#"
try:
    trust:
        2 = 3
    4 = 5
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("try_stmt_unknown_rolls_back_and_returns_success");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "unknown try body should return a successful rolled-back try result:\n{}",
            run_output
        );
        assert!(matches!(
            try_execution(&stmt_results),
            TryStmtExecutionResult::RolledBack(_)
        ));
        assert!(
            run_output.contains("\"kind\": \"RolledBack\"")
                && (run_output.contains("unknown_error") || run_output.contains("try failed")),
            "try should report the unknown inner step:\n{}",
            run_output
        );

        let (stmt_results_after, runtime_error_after) = execute_source("2 = 3", &mut runtime);
        let (run_succeeded_after, run_output_after) =
            render_run_output(&runtime, &stmt_results_after, &runtime_error_after);
        assert!(
            !run_succeeded_after,
            "facts from a failed try should not leak:\n{}",
            run_output_after
        );
    });
}

#[test]
fn try_stmt_error_rolls_back_and_returns_success() {
    run_with_large_stack("try_stmt_error_rolls_back_and_returns_success", || {
        let source_code = r#"
try:
    have a R = 1
    1 / 0 = 0
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("try_stmt_error_rolls_back_and_returns_success");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

        assert!(
            run_succeeded,
            "error try body should return a successful rolled-back try result:\n{}",
            run_output
        );
        assert!(matches!(
            try_execution(&stmt_results),
            TryStmtExecutionResult::RolledBack(_)
        ));
        assert!(
            run_output.contains("arithmetic_error")
                || run_output.contains("1 / 0 = 0")
                || run_output.contains("division"),
            "try should report the failing inner statement:\n{}",
            run_output
        );

        let (stmt_results_after, runtime_error_after) =
            execute_source("have a R = 2", &mut runtime);
        let (run_succeeded_after, run_output_after) =
            render_run_output(&runtime, &stmt_results_after, &runtime_error_after);
        assert!(
            run_succeeded_after,
            "definitions from a failed try should not leak:\n{}",
            run_output_after
        );
    });
}

#[test]
fn rolled_back_try_compiles_as_a_no_effect_statement() {
    let lean_source = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source(
        "try:\n    1 = 0\n1 = 1\n",
        "rolled_back_try_to_lean.lit",
    )
    .expect("a rolled-back try should not block compilation of later statements");

    assert!(!lean_source.contains("1 = 0"), "{lean_source}");
}

#[test]
fn internal_claim_question_goal_remains_supported() {
    run_with_large_stack("internal_claim_question_goal_remains_supported", || {
        let source_code = r#"
claim:
    ? 1 = 1
    1 = 1
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("internal_claim_question_goal_remains_supported");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("internal_claim_question_goal_allows_proof_body");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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
    case 1 = 1
    case 1 != 1:
        impossible 1 = 1

by extension:
    ? {1} = {1}

by for:
    ? forall n range(0, 3) => n < 3

by enumerate finite_set:
    ? forall z {1, 2} => z $in {1, 2}

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("question_goal_is_the_only_goal_syntax");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("bodyless_case_closed");
        let (stmt_results, runtime_error) = execute_source(positive_source, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);
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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("bodyless_case_unclosed");
        let (stmt_results, runtime_error) = execute_source(negative_source, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);
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

by thm bodyless_zero_sides(2) => 2 + 0 = 0 + 2

by induc n from 0:
    ? n = n

by strong_induc m from 0:
    ? m = m
"#;

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("bodyless_by_thm_goal_closed");
        let (results, error) = execute_source(selected_theorem_source, &mut runtime);
        let (succeeded, output) = render_run_output(&runtime, &results, &error);
        assert!(
            succeeded,
            "an inline by-thm selection should use the selected-fact verifier:\n{output}"
        );
        assert!(
            output.contains("by thm bodyless_zero_sides(2) => 2 + 0 = 0 + 2"),
            "inline by-thm output should retain the selected atomic target:\n{output}"
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
            let mut runtime = Runtime::default();
            runtime.start_isolated_source(&format!("bodyless_by_goal_negative_{index}"));
            let (results, error) = execute_source(source, &mut runtime);
            let (succeeded, output) = render_run_output(&runtime, &results, &error);
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
        let mut runtime = Runtime::default();
        runtime.start_isolated_source("prove_is_available_as_an_identifier");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);
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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source("top_level_question_goal_is_rejected");
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("fn_range_intro_subset_and_preimage_work");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("fn_range_membership_infers_preimage_existence");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("have_by_preimage_rejects_non_range_source");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("have_by_preimage_checks_witness_count");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("replacement_requires_binary_prop");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("replacement_requires_uniqueness_over_source_set");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "replacement_membership_infers_preimage_and_preimage_stmt_works",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

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

        let mut runtime = Runtime::default();
        runtime.start_isolated_source("replacement_membership_intro_from_relation_witness");
        let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_output(&runtime, &stmt_results, &runtime_error);

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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "replacement_uniqueness_keeps_outer_same_spelling_parameter_rigid",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);

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

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("nested_forall_reusing_outer_param_is_rejected");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

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

    let mut runtime = Runtime::default();
    runtime
        .start_isolated_source("induction_proof_local_names_do_not_leak_outside_their_proof_block");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

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

    let mut invalid_runtime = Runtime::default();
    invalid_runtime.start_isolated_source("parser_scope_rejects_active_cross_kind_reuse");
    let (invalid_results, invalid_error) =
        execute_source(invalid_source_code, &mut invalid_runtime);
    let (invalid_succeeded, invalid_output) =
        render_run_output(&invalid_runtime, &invalid_results, &invalid_error);
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

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("parser_scope_releases_finished_scopes");
    let (stmt_results, runtime_error) = execute_source(valid_source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "completed sibling scopes must release their spelling:\n{}",
        run_output
    );
}

#[test]
fn failed_scope_begin_does_not_leak_a_partial_binding() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("failed_scope_begin_does_not_leak");

    let (_, first_error) = execute_source("trust have x, x R", &mut runtime);
    assert!(
        first_error.is_some(),
        "the duplicate binding must be rejected"
    );

    let (stmt_results, runtime_error) = execute_source("trust have x R", &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    assert!(
        run_succeeded,
        "a failed scope begin must not leave a partial binding:\n{}",
        run_output
    );
}

#[test]
fn failed_statement_parse_rolls_back_all_new_bindings() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("failed_statement_parse_rolls_back_bindings");

    let (_, first_error) = execute_source("trust have x R, y", &mut runtime);
    assert!(first_error.is_some(), "the incomplete definition must fail");

    let (stmt_results, runtime_error) = execute_source("trust have x R", &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    assert!(
        run_succeeded,
        "a failed statement parse must roll back every new binding:\n{}",
        run_output
    );
}

#[test]
fn trust_statements_skip_well_definedness_and_remain_atomic() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("trust_statements_skip_well_definedness");

    let unchecked_source = r#"
trust:
    777 = 778
    1 / 0 = 0
"#;
    let (unchecked_results, unchecked_error) = execute_source(unchecked_source, &mut runtime);
    assert!(unchecked_error.is_none());
    assert_eq!(unchecked_results.len(), 1);
    assert!(runtime.cache_known_facts_contains("777 = 778").0);
    assert!(runtime.cache_known_facts_contains("1 / 0 = 0").0);

    let unchecked_summary = render_run_summary(RunSummaryRequest {
        runtime: &runtime,
        stmt_results: &unchecked_results,
        runtime_error: &unchecked_error,
    });
    assert!(!unchecked_summary.contains("\"direct_trust\": 0"));

    let strict_source = r#"
trust:
    999 = 1000
    1 / 0 = 0
"#;
    let mut strict_runtime = Runtime::new(RuntimeOptions::strict(
        OutputDetail::Normal,
        OutputLanguage::English,
        SummaryOption::None,
    ));
    strict_runtime.start_isolated_source("strict_trust_is_atomic");
    let (failed_results, failed_error) = execute_source(strict_source, &mut strict_runtime);
    assert!(failed_results.is_empty());
    assert!(failed_error.is_some());
    assert!(!strict_runtime.cache_known_facts_contains("999 = 1000").0);
    assert!(
        runtime.cache_known_facts_contains("777 = 778").0,
        "a separately rejected trust statement cannot affect an earlier committed runtime"
    );
}

#[test]
fn trust_have_skips_well_definedness_and_commits_atomically() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("trust_have_skips_well_definedness");

    let unchecked_source = r#"
trust have rollback_probe R:
    rollback_probe = rollback_probe
    1 / 0 = 0
"#;
    let (unchecked_results, unchecked_error) = execute_source(unchecked_source, &mut runtime);
    assert!(unchecked_error.is_none());
    assert_eq!(unchecked_results.len(), 1);
    assert!(
        runtime.is_name_used_for_identifier("rollback_probe"),
        "the trusted binding and all attached unchecked facts commit together"
    );
    let [StmtResult::Success(SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustHaveStmt(
        unchecked,
    )))] = unchecked_results.as_slice()
    else {
        panic!("expected one dedicated trust-have Result")
    };
    for store in &unchecked.common.infers.store_fact_outputs {
        let fact_id = store.fact_id.expect("trusted store must retain its FactId");
        assert_eq!(
            runtime
                .known_fact_id_for_fact(&store.itself_and_why_itself_is_stored.0)
                .expect("trusted fact lookup should succeed"),
            Some(fact_id)
        );
    }

    let (duplicate_results, duplicate_error) =
        execute_source("trust have rollback_probe R", &mut runtime);
    assert!(duplicate_results.is_empty());
    assert!(duplicate_error.is_some());
    assert!(runtime.is_name_used_for_identifier("rollback_probe"));

    let mut dependent_runtime = Runtime::default();
    dependent_runtime.start_isolated_source("trust_have_keeps_local_prefix_visible");
    let dependent_source = r#"
trust have denominator R:
    denominator != 0
    1 / denominator = 1 / denominator
"#;
    let (dependent_results, dependent_error) =
        execute_source(dependent_source, &mut dependent_runtime);
    let (dependent_succeeded, dependent_output) =
        render_run_output(&dependent_runtime, &dependent_results, &dependent_error);
    assert!(
        dependent_succeeded,
        "later facts must see earlier facts inside the transaction:\n{}",
        dependent_output
    );

    let committed_probe = r#"
denominator != 0
2 / denominator = 2 / denominator
"#;
    let (probe_results, probe_error) = execute_source(committed_probe, &mut dependent_runtime);
    let (probe_succeeded, probe_output) =
        render_run_output(&dependent_runtime, &probe_results, &probe_error);
    assert!(
        probe_succeeded,
        "the complete trust have transaction must be reusable afterward:\n{}",
        probe_output
    );
}

#[test]
fn inline_extension_and_block_for_and_enumerate_keep_proof_routes() {
    let source_code = r#"
by extension {1} = {1}

by extension:
    ? {2} = {2}

by for:
    ? forall m closed_range(0, 2) => m <= 2

by enumerate finite_set:
    ? forall y {3, 4}:
        y = 3 or y = 4
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("inline_extension_and_block_for_and_enumerate_keep_proof_routes");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);

    assert!(
        run_succeeded,
        "extension and goal-block proof methods should use their existing executors:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"kind\": \"ByExtensionStmt\"")
            && run_output.contains("\"kind\": \"ByEnumerateFiniteSetStmt\"")
            && run_output.contains("\"kind\": \"ByForStmt\""),
        "all three proof methods should retain their existing proof provenance:\n{}",
        run_output
    );
}

#[test]
fn proof_method_goal_placement_boundaries_are_explicit() {
    for source_code in [
        "by for forall n range(0, 1) => n < 1",
        "by enumerate finite_set forall n {0} => n = 0",
    ] {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source("removed_inline_proof_goal");
        let (results, error) = execute_source(source_code, &mut runtime);
        let (succeeded, output) = render_run_output(&runtime, &results, &error);
        assert!(
            !succeeded,
            "the removed inline proof goal unexpectedly succeeded: {source_code}"
        );
        assert!(
            output.contains("followed by an indented `? forall ...` goal"),
            "the diagnostic should direct the goal to block form:\n{output}"
        );
    }

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("inline_extension_body_boundary");
    let (results, error) = execute_source("by extension {1} = {1}:\n    1 = 1", &mut runtime);
    let (succeeded, output) = render_run_output(&runtime, &results, &error);
    assert!(!succeeded, "inline extension accepted a body:\n{output}");
    assert!(
        output.contains("does not accept an indented body"),
        "{output}"
    );
}

#[test]
fn by_enumerate_finite_set_resolves_named_literal_definition() {
    let source_code = r#"
have P finite_set = {1, 2}

by enumerate finite_set:
    ? forall x P:
        x = 1 or x = 2
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("by_enumerate_finite_set_resolves_named_literal_definition");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source("anonymous_quotient_lambda_uses_nonzero_on_predicate");
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);
            assert!(
                run_succeeded,
                "anonymous quotient lambda should inherit nonzero-on facts:\n{}",
                run_output
            );
            assert!(
                run_output.contains(
                    "fn membership: same input domain and pointwise values lie in the target return set"
                ),
                "moving anonymous membership into the InFact owner must preserve its existing certificate:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn anonymous_function_alpha_equivalent_signature_uses_membership_builtin() {
    let source_code = r#"
forall E set:
    fn(y E) R {0} $in fn(x E) R
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source(
        "anonymous_function_alpha_equivalent_signature_uses_membership_builtin",
    );
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
    assert!(
        run_succeeded,
        "alpha-equivalent anonymous signature membership failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains(
            "fn membership: same input domain and pointwise values lie in the target return set"
        ),
        "alpha-equivalent anonymous membership should preserve its pointwise certificate:\n{}",
        run_output
    );
}

#[test]
fn anonymous_quotient_lambda_without_nonzero_premise_is_rejected() {
    let source_code = r#"
forall E power_set(R), f, g fn(x E) R:
    fn(x E) R {f(x) / g(x)} $in fn(x E) R
"#;

    let mut runtime = Runtime::default();
    runtime.start_isolated_source("anonymous_quotient_lambda_without_nonzero_premise_is_rejected");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    let (run_succeeded, run_output) = render_run_output(&runtime, &stmt_results, &runtime_error);
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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "anonymous_quotient_lambda_in_existential_respects_nonzero_on_predicate",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);
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
    let setup = r#"
prop nonzero(value R):
    value != 0
"#;

    let mut runtime = Runtime::default();
    runtime
        .start_isolated_source("existential_well_definedness_uses_preceding_predicate_definition");
    let (setup_results, setup_error) = execute_source(setup, &mut runtime);
    assert!(
        setup_error.is_none(),
        "{}",
        render_run_output(&runtime, &setup_results, &setup_error).1
    );
    let fact = parse_fact_for_wd(
        &mut runtime,
        "exist denominator R st {$nonzero(denominator), 1 / denominator = 1 / denominator}",
        "existential_wd_uses_preceding_predicate",
    );
    runtime
        .verify_fact_well_defined_result(&fact, &VerifyState::initial())
        .expect("a preceding predicate condition should establish the later divisor obligation");
}

#[test]
fn existential_well_definedness_still_requires_a_nonzero_premise() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("existential_well_definedness_still_requires_a_nonzero_premise");
    let fact = parse_fact_for_wd(
        &mut runtime,
        "exist denominator R st {1 / denominator = 1 / denominator}",
        "existential_wd_requires_nonzero",
    );
    let error = runtime
        .verify_fact_well_defined_result(&fact, &VerifyState::initial())
        .expect_err("division without a preceding nonzero premise must remain ill-defined");
    let run_output = error.trace_message();
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

            let mut runtime = Runtime::default();
            runtime.start_isolated_source(
                "anonymous_quotient_lambda_over_punctured_set_is_well_defined",
            );
            let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_output(&runtime, &stmt_results, &runtime_error);
            assert!(
                run_succeeded,
                "anonymous quotient lambda over a punctured set should be well-defined:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_zorn_lemma_stores_named_maximal_element_exist_fact() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)
prop is_upper_bound(c power_set(s), u s):
    forall x c:
        $leq(x, u)
prop is_maximal(m s):
    forall x s:
        $leq(m, x)
        =>:
            x = m

by zorn_lemma: set s, prop leq, prop is_upper_bound, prop is_maximal:
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
        forall c power_set(s):
            forall x, y c:
                $leq(x, y) or $leq(y, x)
            =>:
                exist u s st {$is_upper_bound(c, u)}

exist m s st {$is_maximal(m)}
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_stores_named_maximal_element_exist_fact",
    );
    assert!(
        run_succeeded,
        "named-property Zorn interface should store its conclusion:\n{run_output}"
    );
}

#[test]
fn by_zorn_lemma_rejects_wrong_upper_bound_definition() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)
prop wrong_upper_bound(c power_set(s), u s):
    forall x c:
        $leq(u, x)
prop is_maximal(m s):
    forall x s:
        $leq(m, x)
        =>:
            x = m

by zorn_lemma: set s, prop leq, prop wrong_upper_bound, prop is_maximal
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_rejects_wrong_upper_bound_definition",
    );
    assert!(!run_succeeded, "wrong upper-bound meaning must fail");
    assert!(
        run_output.contains("must have exactly the definition"),
        "failure should identify the required upper-bound definition:\n{run_output}"
    );
}

#[test]
fn by_zorn_lemma_rejects_wrong_maximality_definition() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)
prop is_upper_bound(c power_set(s), u s):
    forall x c:
        $leq(x, u)
prop wrong_maximal(m s):
    forall x s:
        $leq(x, m)
        =>:
            x = m

by zorn_lemma: set s, prop leq, prop is_upper_bound, prop wrong_maximal
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_rejects_wrong_maximality_definition",
    );
    assert!(!run_succeeded, "wrong maximality meaning must fail");
    assert!(
        run_output.contains("must have exactly the definition"),
        "failure should identify the required maximality definition:\n{run_output}"
    );
}

#[test]
fn by_zorn_lemma_without_trailing_colon_checks_obligations() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)
prop is_upper_bound(c power_set(s), u s):
    forall x c:
        $leq(x, u)
prop is_maximal(m s):
    forall x s:
        $leq(m, x)
        =>:
            x = m

by zorn_lemma: set s, prop leq, prop is_upper_bound, prop is_maximal
"#;

    let (run_succeeded, run_output) = run_zorn_lemma_regression_source(
        source_code,
        "by_zorn_lemma_without_trailing_colon_checks_obligations",
    );
    assert!(!run_succeeded, "missing Zorn obligations must fail");
    assert!(
        run_output.contains("nonempty obligation"),
        "the syntax should reach obligation checking:\n{run_output}"
    );
}

fn run_zorn_lemma_regression_source(source_code: &str, file_label: &str) -> (bool, String) {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source(file_label);
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    render_run_output(&runtime, &stmt_results, &runtime_error)
}

#[test]
fn by_axiom_of_choice_stores_named_choice_function_exist_fact() {
    let source_code = r#"
have S set

by axiom_of_choice: set S:
    trust forall A S:
        $is_nonempty_set(A)

exist f fn(A S) family_union(S) st {$is_choice_function_for(S, S, fn(A S) S {A}, f)}
obtain chooser from exist f fn(A S) family_union(S) st {$is_choice_function_for(S, S, fn(A S) S {A}, f)}
forall A S:
    chooser(A) $in A
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_stores_named_choice_function_exist_fact",
    );
    assert!(
        run_succeeded,
        "choice should store an atomic named-property existential:\n{run_output}"
    );
}

#[test]
fn by_axiom_of_choice_result_retains_typed_target_facts_roles_and_fact_ids() {
    let source_code = r#"
have S set

by axiom_of_choice: set S:
    trust forall A S:
        $is_nonempty_set(A)
"#;
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("by_axiom_of_choice_structured_result");
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    assert!(runtime_error.is_none(), "{runtime_error:?}");
    let result = stmt_results
        .iter()
        .find_map(|result| match result {
            StmtResult::Success(SuccessStmtResult::By(
                SuccessByStmtResult::ByAxiomOfChoiceStmt(result),
            )) => Some(result.as_ref()),
            _ => None,
        })
        .expect("expected successful axiom-of-choice result");
    let verification = result.verification.as_ref().expect("retained verification");
    assert_eq!(
        verification.proof_kind,
        SuccessVerifyByChoiceProofKind::AxiomOfChoice
    );
    let SuccessVerifyByChoiceTargetResult::AxiomOfChoice { family } = &verification.target else {
        panic!("choice target must retain the exact family object")
    };
    assert_eq!(
        obj_equality_key(family),
        obj_equality_key(&result.statement.family)
    );
    assert_eq!(
        verification
            .obligations
            .iter()
            .map(|obligation| obligation.role)
            .collect::<Vec<_>>(),
        vec![
            SuccessVerifyByChoiceObligationRole::ChoiceFamilyIsSet,
            SuccessVerifyByChoiceObligationRole::ChoiceMembersNonempty,
        ]
    );
    assert!(verification
        .obligations
        .iter()
        .all(|obligation| !obligation.fact.to_string().is_empty()));
    assert!(verification
        .trusted_conclusion
        .to_string()
        .starts_with("exist "));
}

#[test]
fn by_axiom_of_choice_named_property_keeps_outer_family_rigid() {
    let source_code = r#"
claim:
    ? forall A set:
        forall member A:
            $is_nonempty_set(member)
        =>:
            exist f fn(member A) family_union(A) st {$is_choice_function_for(A, A, fn(member A) A {member}, f)}
    by axiom_of_choice: set A:
        forall member A:
            $is_nonempty_set(member)
    exist f fn(member A) family_union(A) st {$is_choice_function_for(A, A, fn(member A) A {member}, f)}
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_named_property_keeps_outer_family_rigid",
    );
    assert!(
        run_succeeded,
        "generated choice binders must not capture outer `A`:\n{run_output}"
    );
}

#[test]
fn by_axiom_of_choice_reports_missing_members_nonempty() {
    let source_code = r#"
have S set

by axiom_of_choice: set S:
    1 = 1
"#;

    let (run_succeeded, run_output) = run_axiom_of_choice_regression_source(
        source_code,
        "by_axiom_of_choice_reports_missing_members_nonempty",
    );
    assert!(!run_succeeded, "missing choice obligation must fail");
    assert!(
        run_output.contains("members_nonempty obligation"),
        "failure should name the missing obligation:\n{run_output}"
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
    let mut runtime = Runtime::default();
    runtime.start_isolated_source(file_label);
    let (stmt_results, runtime_error) = execute_source(source_code, &mut runtime);
    render_run_output(&runtime, &stmt_results, &runtime_error)
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
                run_output.contains("\"kind\": \"ByRegularityAxiomStmt\""),
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
        "by cases 1 = 1:\n    case 1 = 1",
        "by contra 1 = 1:\n    impossible 1 != 1",
    ];

    for (index, source_code) in cases.iter().enumerate() {
        let mut runtime = Runtime::default();
        runtime.start_isolated_source(&format!("removed_by_header_{}", index));
        let (results, error) = execute_source(source_code, &mut runtime);
        let (succeeded, output) = render_run_output(&runtime, &results, &error);
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
