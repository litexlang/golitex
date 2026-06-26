use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;
use crate::to_latex::to_latex_from_source_after_builtins;
use crate::to_python::to_python_from_source_after_builtins;

use super::helper::run_with_large_stack;

fn legacy_acceptance_field_name() -> String {
    ["accepted", "by"].join("_")
}

fn assert_no_legacy_acceptance_field(run_output: &str, context: &str) {
    let field_name = legacy_acceptance_field_name();
    assert!(
        !run_output.contains(&format!("\"{}\"", field_name)),
        "{} output should not expose legacy acceptance field:\n{}",
        context,
        run_output
    );
}

#[test]
fn builtin_rules_do_not_call_full_verifier_pipeline() {
    let builtin_rules_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("verify")
        .join("verify_builtin_rules");
    let disallowed_calls = [
        "verify_fact(",
        "verify_atomic_fact(",
        "verify_forall_fact(",
        "verify_exist_or_and_chain_atomic_fact(",
        "verify_or_and_chain_atomic_fact(",
    ];
    let mut violations = Vec::new();

    for entry in fs::read_dir(&builtin_rules_dir).expect("read verify_builtin_rules dir") {
        let entry = entry.expect("read verify_builtin_rules entry");
        let path = entry.path();
        if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
            continue;
        }
        let content = fs::read_to_string(&path).expect("read verify_builtin_rules source file");
        for (line_index, line) in content.lines().enumerate() {
            for disallowed_call in disallowed_calls {
                if line.contains(disallowed_call) {
                    violations.push(format!(
                        "{}:{} contains `{}`",
                        path.display(),
                        line_index + 1,
                        disallowed_call
                    ));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "builtin rules must use restricted known-atomic/builtin helpers, not the full verifier:\n{}",
        violations.join("\n")
    );
}

#[test]
fn latex_output_is_fragment_without_default_packages() {
    let output = to_latex_from_source_after_builtins(
        "1 = 1",
        "latex_output_is_fragment_without_default_packages",
    )
    .expect("simple Litex source should convert to LaTeX");

    assert!(output.contains(r"\["));
    assert!(output.contains(r"\]"));
    assert!(output.contains("1 = 1"));
    assert!(!output.contains(r"\documentclass{article}"));
    assert!(!output.contains(r"\begin{document}"));
    assert!(!output.contains(r"\end{document}"));
    assert!(!output.contains(r"\paragraph{Stmt 1}"));
    assert!(!output.contains(r"\usepackage{amsmath}"));
    assert!(!output.contains(r"\usepackage{amssymb}"));
}

#[test]
fn python_extractor_outputs_supported_have_subset() {
    run_with_large_stack("python_extractor_outputs_supported_have_subset", || {
        let source_code = r#"
have q Q = 1
have z Z = 3

have fn as algo f(x R) R = x + 1
have fn as algo g(x R) R = f(x) + 2

have fn as algo max2(x, y R) R by cases:
    case x >= y: x
    case x < y: y
"#;

        let output = to_python_from_source_after_builtins(
            source_code,
            "python_extractor_outputs_supported_have_subset",
        )
        .expect("supported Python extraction should succeed");

        assert!(output.contains("q = 1.0"));
        assert!(output.contains("z = 3.0"));
        assert!(output.contains("def f(x):"));
        assert!(output.contains("return (x + 1.0)"));
        assert!(output.contains("def g(x):"));
        assert!(output.contains("return (f(x) + 2.0)"));
        assert!(output.contains("def max2(x, y):"));
        assert!(output.contains("if x >= y:"));
        assert!(output.contains("elif x < y:"));
        assert!(output.contains("unreachable verified Litex cases"));
    });
}

#[test]
fn python_extractor_skips_non_numeric_have_obj_equal() {
    run_with_large_stack("python_extractor_skips_non_numeric_have_obj_equal", || {
        let output = to_python_from_source_after_builtins(
            "have s set = R",
            "python_extractor_skips_non_numeric_have_obj_equal",
        )
        .expect("non-numeric object definitions should be skipped");

        assert_eq!(output, "# No Python-extractable Litex definitions.");
    });
}

#[test]
fn python_extractor_rejects_standalone_algo() {
    run_with_large_stack("python_extractor_rejects_standalone_algo", || {
        let source_code = r#"
have fn f(x R) R = x

algo f(x):
    x
"#;

        let error = to_python_from_source_after_builtins(
            source_code,
            "python_extractor_rejects_standalone_algo",
        )
        .expect_err("standalone algo should not be extracted in v1");
        let error_text = format!("{:?}", error);
        assert!(error_text.contains("does not support standalone `algo`"));
    });
}

#[test]
fn python_extractor_rejects_non_real_function_parameters() {
    run_with_large_stack(
        "python_extractor_rejects_non_real_function_parameters",
        || {
            let source_code = "have fn as algo f(x Z) R = x";
            let error = to_python_from_source_after_builtins(
                source_code,
                "python_extractor_rejects_non_real_function_parameters",
            )
            .expect_err("non-R function params should be rejected by Python extraction");
            let error_text = format!("{:?}", error);
            assert!(error_text.contains("supports only `R` function parameters"));
        },
    );
}

#[test]
fn list_set_membership_implies_equality_or() {
    let source_code = r#"
forall a set:
    a = 1 or a = 2 or a = 3
    =>:
        a $in {1, 2, 3}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("list_set_membership_implies_equality_or");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "list_set_membership_implies_equality_or failed:\n{}",
        run_output
    );
}

#[test]
fn sketch_stmt_is_checked_and_local() {
    let source_code = r#"
sketch:
    know:
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
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

    know:
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

            let env = runtime
                .environment_stack
                .last()
                .expect("runtime should have a current environment");
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
    know:
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
fn top_level_scratch_is_rejected_with_sketch_hint() {
    let source_code = r#"
scratch:
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("top_level_scratch_is_rejected_with_sketch_hint");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "top-level scratch should be rejected:\n{}",
        run_output
    );
    assert!(
        run_output.contains("top-level `scratch:` has been replaced by `sketch:`"),
        "top-level scratch should explain the replacement:\n{}",
        run_output
    );
}

#[test]
fn top_level_prove_is_rejected_with_sketch_hint() {
    let source_code = r#"
prove:
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("top_level_prove_is_rejected_with_sketch_hint");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "top-level prove should be rejected:\n{}",
        run_output
    );
    assert!(
        run_output.contains("top-level `prove:` is not supported; use `sketch:`"),
        "top-level prove should explain the supported spelling:\n{}",
        run_output
    );
}

#[test]
fn internal_claim_prove_block_remains_supported() {
    run_with_large_stack("internal_claim_prove_block_remains_supported", || {
        let source_code = r#"
claim:
    prove:
        1 = 1
    1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("internal_claim_prove_block_remains_supported");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "internal claim prove block should still run:\n{}",
            run_output
        );
    });
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

    a(1) $in fn_range_on(a, 1...3)
    a(2) $in fn_range_on(a, 1...3)
    fn_range_on(a, 1...3) $subset R
    fn_range_on(a, 1...3) $in power_set(R)
    $is_finite_set(fn_range_on(a, 1...3))
    count(fn_range_on(a, 1...3)) $in N

    have by preimage k from a(2) $in fn_range_on(a, 1...3)
    k $in 1...3
    a(2) = a(k)
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
fn fn_range_on_rejects_non_unary_function() {
    let source_code = r#"
sketch:
    have g fn(x R, y R) R
    fn_range_on(g, R) $subset R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("fn_range_on_rejects_non_unary_function");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "fn_range_on with non-unary function should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("fn_range_on expects a unary function"),
        "fn_range_on non-unary error should be explicit:\n{}",
        run_output
    );
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

know forall x {3, 5, 9}, y, y2 set:
    $rel(x, y)
    $rel(x, y2)
    =>:
        y = y2

have B set = replacement(rel, {3, 5, 9})

forall y B:
    exist x {3, 5, 9} st {$rel(x, y)}

have y set
know y $in replacement(rel, {3, 5, 9})
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
fn typed_fn_return_standard_subset_allows_floor_bounds_for_reals() {
    run_with_large_stack(
        "typed_fn_return_standard_subset_allows_floor_bounds_for_reals_large_stack",
        || {
            let source_code = r#"
import Int

claim:
    prove:
        forall x R:
            exist n Z st {n <= x and x < n + 1}
    Int::floor(x) $in R
    by thm Int::floor_bounds(x)
    Int::floor(x) <= x < Int::floor(x) + 1
    witness exist n Z st {n <= x and x < n + 1} from Int::floor(x):
        Int::floor(x) <= x and x < Int::floor(x) + 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "typed_fn_return_standard_subset_allows_floor_bounds_for_reals",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "typed_fn_return_standard_subset_allows_floor_bounds_for_reals failed:\n{}",
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
by for forall! n range(0, 3): n < 3

by enumerate finite_set forall! x {1, 2}: x $in {1, 2}
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
fn by_zorn_lemma_stores_maximal_element_exist_fact() {
    let source_code = r#"
have s set
abstract_prop leq(x, y)

by zorn_lemma: set s, prop leq:
    know $is_nonempty_set(s)
    know:
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
                exist u s st {forall! x C: {$leq(x, u)}}

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
    know $is_nonempty_set(s)
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
    know $is_nonempty_set(s)
    know:
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
    know $is_nonempty_set(s)
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
    know forall A S:
        $is_nonempty_set(A)

exist f fn(A S) cup(S) st {forall! A S: {f(A) $in A}}
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
know forall A S:
    $is_nonempty_set(A)

by axiom_of_choice: set S

exist f fn(A S) cup(S) st {forall! A S: {f(A) $in A}}
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
    know forall A S:
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
let s nonempty_set:
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
know $is_nonempty_set({1, 2})

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
fn have_by_exist_body_well_defined_can_use_forall_domain_fact() {
    let source_code = r#"
prop image_like(S, T set, f fn(x S) T, A, B set):
    A $subset S
    forall y B:
        exist a A st {y = f(a)}

claim:
    prove:
        forall S, T set, f fn(x S) T, A, B set, x S:
            A $subset S
            $image_like(S, T, f, A, B)
            f(x) $in B
            =>:
                x = x
    claim:
        prove:
            forall a A:
                a $in S
        a $in S
    have by exist a A st {f(x) = f(a)}: a
    a $in S
    f(x) = f(a)
    x = x
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "have_by_exist_body_well_defined_can_use_forall_domain_fact",
    );
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "have_by_exist_body_well_defined_can_use_forall_domain_fact failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"object definition by existence\""),
        "have by exist should report the semantic statement type:\n{}",
        run_output
    );
    assert_no_legacy_acceptance_field(&run_output, "have by exist");
    assert!(
        !run_output.contains("HaveExistObjStmt"),
        "have by exist should not report the legacy statement type:\n{}",
        run_output
    );
}

#[test]
fn anonymous_fn_restrict_requires_valid_target_domain_and_return() {
    run_with_large_stack(
        "anonymous_fn_restrict_requires_valid_target_domain_and_return_large_stack",
        || {
            anonymous_fn_restrict_positive_cases_impl();
            anonymous_fn_restrict_negative_case_impl();
        },
    );
}

fn anonymous_fn_restrict_positive_cases_impl() {
    let positive_source_code = r#"
$restricts_to('R(x){x}, fn(x closed_range(1, 2)) R)
$restricts_to('R(x){x + 1}, fn(x closed_range(1, 2)) R)
$restricts_to('(x R: x > 0) R {x}, fn(x N_pos) R)
$restricts_to('R(x){x}, fn(x closed_range(1, 2)) N)
"#;

    let mut positive_runtime = Runtime::new_with_builtin_code();
    positive_runtime.new_file_path_new_env_new_name_scope("anonymous_fn_restrict_positive");
    let (positive_stmt_results, positive_runtime_error) =
        run_source_code(positive_source_code, &mut positive_runtime);
    let (positive_run_succeeded, positive_run_output) = render_run_source_code_output(
        &positive_runtime,
        &positive_stmt_results,
        &positive_runtime_error,
        false,
    );
    assert!(
        positive_run_succeeded,
        "anonymous fn restrict positive cases failed:\n{}",
        positive_run_output
    );
}

fn anonymous_fn_restrict_negative_case_impl() {
    let negative_source_code = r#"
$restricts_to('(x R: x > 0) R {x}, fn(x closed_range(-1, 1)) R)
"#;

    let mut negative_runtime = Runtime::new_with_builtin_code();
    negative_runtime.new_file_path_new_env_new_name_scope("anonymous_fn_restrict_negative");
    let (negative_stmt_results, negative_runtime_error) =
        run_source_code(negative_source_code, &mut negative_runtime);
    let (negative_run_succeeded, negative_run_output) = render_run_source_code_output(
        &negative_runtime,
        &negative_stmt_results,
        &negative_runtime_error,
        false,
    );
    assert!(
        !negative_run_succeeded,
        "anonymous fn restrict negative case should fail:\n{}",
        negative_run_output
    );
    assert!(
        negative_run_output.contains("failed to verify function domain fact"),
        "negative case should explain the domain failure:\n{}",
        negative_run_output
    );
}

#[test]
fn anonymous_fn_direct_equality_uses_pointwise_extensionality() {
    let positive_source_code = r#"
'R(x){x} = 'R(y){y}

forall f, g fn(x R) R:
    'R(x){f(x) + g(x)} = 'R(x){g(x) + f(x)}

forall f, g fn(x R) R:
    'R(x){f(x) + g(x)} = 'R(x){'R(y){f(y)}(x) + 'R(y){g(y)}(x)}

'(x R: x > 0) R {x} = '(y R: y > 0) R {y}
"#;

    let mut positive_runtime = Runtime::new_with_builtin_code();
    positive_runtime.new_file_path_new_env_new_name_scope(
        "anonymous_fn_direct_equality_uses_pointwise_extensionality_positive",
    );
    let (positive_stmt_results, positive_runtime_error) =
        run_source_code(positive_source_code, &mut positive_runtime);
    let (positive_run_succeeded, positive_run_output) = render_run_source_code_output(
        &positive_runtime,
        &positive_stmt_results,
        &positive_runtime_error,
        false,
    );
    assert!(
        positive_run_succeeded,
        "anonymous fn direct equality should use pointwise extensionality:\n{}",
        positive_run_output
    );

    let negative_source_code = r#"
'(x N) R {x} = 'R(x){x}
"#;

    let mut negative_runtime = Runtime::new_with_builtin_code();
    negative_runtime.new_file_path_new_env_new_name_scope(
        "anonymous_fn_direct_equality_uses_pointwise_extensionality_negative",
    );
    let (negative_stmt_results, negative_runtime_error) =
        run_source_code(negative_source_code, &mut negative_runtime);
    let (negative_run_succeeded, negative_run_output) = render_run_source_code_output(
        &negative_runtime,
        &negative_stmt_results,
        &negative_runtime_error,
        false,
    );
    assert!(
        !negative_run_succeeded,
        "anonymous fn direct equality should not ignore domain differences:\n{}",
        negative_run_output
    );
}

#[test]
fn curried_have_fn_equal_unfolds_pointwise() {
    let source_code = r#"
have fn seq_add(a, b seq(R)) fn(k N_pos) R = '(n N_pos) R {a(n) + b(n)}

forall a, b seq(R), k N_pos:
    seq_add(a, b)(k) = a(k) + b(k)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("curried_have_fn_equal_unfolds_pointwise");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "curried have fn equality should unfold pointwise:\n{}",
        run_output
    );
}

#[test]
fn fn_application_returning_fn_set_verifies_sequence_membership() {
    let source_code = r#"
have fn seq_add(a, b seq(R)) fn(k N_pos) R = '(n N_pos) R {a(n) + b(n)}

forall a, b seq(R):
    seq_add(a, b) $in seq(R)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "fn_application_returning_fn_set_verifies_sequence_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "function application returning a fn set should verify seq membership:\n{}",
        run_output
    );
}

#[test]
fn set_valued_have_fn_application_unfolds_for_membership() {
    let source_code = r#"
have fn circle(r R_pos) power_set(cart(R, R)) = {x cart(R, R): x[1]^2 + x[2]^2 = r^2}
have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {x cart(R, R): a * x[1] + b * x[2] + c = 0}

(3, 4) $in circle(5)
(2, 2) $in line(1, -1, 0)

forall a, b R:
    a != 0 or b != 0
    =>:
        (0, 0) $in line(a, b, 0)

forall p cart(R, R):
    p $in circle(5)
    =>:
        p[1]^2 + p[2]^2 = 5^2
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "set_valued_have_fn_application_unfolds_for_membership",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "set-valued have fn applications should unfold for membership:\n{}",
        run_output
    );
}

#[test]
fn set_valued_have_fn_application_keeps_side_conditions() {
    let source_code = r#"
have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {x cart(R, R): a * x[1] + b * x[2] + c = 0}

(0, 0) $in line(0, 0, 0)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "set_valued_have_fn_application_keeps_side_conditions",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "set-valued have fn unfolding should not bypass argument side conditions:\n{}",
        run_output
    );
}

#[test]
fn unary_numeric_objects_respect_argument_equality() {
    let source_code = r#"
forall x, y R:
    x = y
    =>:
        abs(x) = abs(y)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("unary_numeric_objects_respect_argument_equality");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "unary numeric objects should respect argument equality:\n{}",
        run_output
    );
}

#[test]
fn iterated_operator_equality_uses_fn_eq_for_function_arg() {
    let positive_source_code = r#"
sum(1, 3, 'Z(x){x}) = sum(1, 3, 'Z(y){y})
product(1, 3, 'Z(x){x}) = product(1, 3, 'Z(y){y})

forall f, g fn(x Z) Z:
    sum(1, 3, 'Z(x){f(x) + g(x)}) = sum(1, 3, 'Z(y){g(y) + f(y)})

forall f, g fn(x Z) Z:
    product(1, 3, 'Z(x){f(x) * g(x)}) = product(1, 3, 'Z(y){g(y) * f(y)})
"#;

    let mut positive_runtime = Runtime::new_with_builtin_code();
    positive_runtime
        .new_file_path_new_env_new_name_scope("iterated_operator_equality_fn_eq_positive");
    let (positive_stmt_results, positive_runtime_error) =
        run_source_code(positive_source_code, &mut positive_runtime);
    let (positive_run_succeeded, positive_run_output) = render_run_source_code_output(
        &positive_runtime,
        &positive_stmt_results,
        &positive_runtime_error,
        false,
    );
    assert!(
        positive_run_succeeded,
        "sum/product equality should compare function args by fn_eq:\n{}",
        positive_run_output
    );

    let negative_source_code = r#"
product(1, 3, 'Z(x){x}) = product(1, 4, 'Z(y){y})
"#;

    let mut negative_runtime = Runtime::new_with_builtin_code();
    negative_runtime
        .new_file_path_new_env_new_name_scope("iterated_operator_equality_fn_eq_negative");
    let (negative_stmt_results, negative_runtime_error) =
        run_source_code(negative_source_code, &mut negative_runtime);
    let (negative_run_succeeded, negative_run_output) = render_run_source_code_output(
        &negative_runtime,
        &negative_stmt_results,
        &negative_runtime_error,
        false,
    );
    assert!(
        !negative_run_succeeded,
        "product equality should still require equal ranges:\n{}",
        negative_run_output
    );
}

#[test]
fn finite_set_sum_core_rules() {
    let source_code = r#"
finite_set_sum({1, 2, 3}, 'Z(x){x}) = 1 + 2 + 3
finite_set_sum({}, 'Z(x){x}) = 0
finite_set_sum(1...3, 'Z(x){x}) = sum(1, 3, 'Z(x){x})
finite_set_sum({1, 2}, 'Z(x){x}) $in Z
finite_set_sum({1, 2}, 'N_pos(x){x}) $in N_pos

sketch:
    have X finite_set
    have c Z
    finite_set_sum(X, '(x X) Z {c}) = count(X) * c

sketch:
    have X power_set(Z)
    know $is_finite_set(X)
    finite_set_sum(X, '(x X) Z {x + 0}) = finite_set_sum(X, '(x X) Z {x})
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("finite_set_sum_core_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite_set_sum core rules should verify:\n{}",
        run_output
    );
}

#[test]
fn finite_set_product_core_rules() {
    let source_code = r#"
finite_set_product({2, 3, 4}, 'Z(x){x}) = 2 * 3 * 4
finite_set_product({}, 'Z(x){x}) = 1
finite_set_product(1...3, 'Z(x){x}) = product(1, 3, 'Z(x){x})
finite_set_product({1, 2}, 'Z(x){x}) $in Z
finite_set_product({1, 2}, 'N_pos(x){x}) $in N_pos
finite_set_product({}, 'N_pos(x){x}) $in N_pos

sketch:
    have X finite_set
    have c R
    finite_set_product(X, '(x X) R {c}) = c ^ count(X)

sketch:
    have X power_set(Z)
    know $is_finite_set(X)
    finite_set_product(X, '(x X) Z {x + 0}) = finite_set_product(X, '(x X) Z {x})
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("finite_set_product_core_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "finite_set_product core rules should verify:\n{}",
        run_output
    );
}

#[test]
fn dependent_fn_param_set_uses_previous_arg() {
    run_with_large_stack(
        "dependent_fn_param_set_uses_previous_arg_large_stack",
        || {
            let source_code = r#"
have f fn(n N_pos, x closed_range(1, n)) R
f(3, 2) = f(3, 2)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime
                .new_file_path_new_env_new_name_scope("dependent_fn_param_set_uses_previous_arg");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "dependent_fn_param_set_uses_previous_arg failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn fn_return_set_cannot_depend_on_params() {
    let source_code = r#"
have f fn(n N_pos) closed_range(1, n)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("fn_return_set_cannot_depend_on_params");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "dependent return set should fail, but succeeded:\n{}",
        run_output
    );
    assert!(
        run_output.contains("function return set cannot depend on function parameters [n]"),
        "dependent return set failure had unexpected output:\n{}",
        run_output
    );
}

#[test]
fn known_equality_implies_weak_order() {
    let source_code = r#"
have a, b R
know a = b
a <= b
a >= b
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("known_equality_implies_weak_order");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known_equality_implies_weak_order failed:\n{}",
        run_output
    );
}

#[test]
fn known_forall_membership_uses_standard_set_subset_direction() {
    let source_code = r#"
abstract_prop p(x)
have x set
know:
    forall u set:
        $p(u)
        =>:
            u $in Z
know $p(x)
x $in Q
x $in R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_membership_uses_standard_set_subset_direction",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall with `u $in Z` should prove broader memberships:\n{}",
        run_output
    );
}

#[test]
fn known_forall_membership_narrowing_requires_known_fact() {
    let source_code = r#"
abstract_prop p(x)
have x set
know:
    forall u set:
        $p(u)
        =>:
        u $in R
know $p(x)
x $in Z
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_membership_narrowing_requires_known_fact",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "`u $in R` should not prove narrower `x $in Z` without a known `x $in Z` fact:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_uses_indexed_function_head() {
    let source_code = r#"
have f fn(x R) R
know forall a R:
    f(a) = a
f(1) = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("known_forall_equality_uses_indexed_function_head");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "indexed equality-in-forall should prove matching function applications:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_indexes_forall_param_side_as_wildcard() {
    let source_code = r#"
have f fn(x R) R
know forall a R:
    a = f(a)
1 + 1 = f(1 + 1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_equality_indexes_forall_param_side_as_wildcard",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param equality side should match non-atom target sides:\n{}",
        run_output
    );
}

#[test]
fn known_forall_equality_with_forall_param_function_head_uses_fallback_bucket() {
    let source_code = r#"
have g fn(x R) R
know forall f fn(x R) R, a R:
    f(a) = a
g(1) = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_equality_with_forall_param_function_head_uses_fallback_bucket",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param function heads should be checked through the fallback equality bucket:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_forall_param_arg_as_wildcard() {
    let source_code = r#"
abstract_prop p(x)
know forall x R:
    $p(x)
$p(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_prop_indexes_forall_param_arg_as_wildcard",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param prop arg should match concrete target args through arg-shape index:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_expression_arg_shape() {
    let source_code = r#"
abstract_prop p(x)
know forall x R:
    $p(x + 1)
$p(1 + 1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("known_forall_prop_indexes_expression_arg_shape");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "expression prop args should be indexed by their top-level operator shape:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_indexes_multi_arg_shape() {
    let source_code = r#"
abstract_prop p(a, b)
know forall a, b R:
    $p(a, b + 1)
$p(2, 3 + 1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("known_forall_prop_indexes_multi_arg_shape");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "multi-arg prop facts should match wildcard and exact arg-shape positions:\n{}",
        run_output
    );
}

#[test]
fn known_forall_prop_with_forall_param_function_head_uses_fallback_bucket() {
    let source_code = r#"
abstract_prop p(x)
have g fn(x R) R
know forall f fn(x R) R:
    $p(f(2))
$p(g(2))
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_prop_with_forall_param_function_head_uses_fallback_bucket",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "forall-param function heads in prop args should be checked through the fallback bucket:\n{}",
        run_output
    );
}

#[test]
fn known_forall_matches_function_param_application_inside_anonymous_fn_body() {
    let source_code = r#"
abstract_prop p(x)

know forall f, g fn(x R) R:
    $p(f)
    $p(g)
    =>:
        $p('R(x){f(x) + g(x)})

claim:
    prove:
        forall a, b, c fn(x R) R:
            $p(a)
            $p(b)
            $p(c)
            =>:
                $p('R(x){a(x) + (b(x) + c(x))})
    $p('R(x){b(x) + c(x)})
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_matches_function_param_application_inside_anonymous_fn_body",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "known forall should infer g = anonymous fn from g(x) inside the anonymous body:\n{}",
        run_output
    );
}

#[test]
fn known_forall_does_not_infer_function_from_single_point_application() {
    let source_code = r#"
abstract_prop p(x)

know forall g fn(x R) R:
    $p('R(x){g(0)})

have h fn(x R) R
$p('R(x){h(x)})
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "known_forall_does_not_infer_function_from_single_point_application",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "known forall should not infer a whole function from a single point application:\n{}",
        run_output
    );
}

#[test]
fn eval_recursive_algo_memoizes_overlapping_calls() {
    run_with_large_stack(
        "eval_recursive_algo_memoizes_overlapping_calls_large_stack",
        || {
            let source_code = r#"
sketch:
    have fib fn(x R) R

    know:
        forall x R:
            x = 0
            =>:
                fib(x) = 0

        forall x R:
            x = 1
            =>:
                fib(x) = 1

        forall x R:
            x > 1
            =>:
                fib(x) = fib(x - 1) + fib(x - 2)

    algo fib(x):
        case x = 0: 0
        case x = 1: 1
        fib(x - 1) + fib(x - 2)

    eval fib(25)
    fib(25) = 75025
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "eval_recursive_algo_memoizes_overlapping_calls",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "eval_recursive_algo_memoizes_overlapping_calls failed:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn pow_with_nonnegative_base_and_positive_real_exponent_is_well_defined() {
    let source_code = r#"
have fn half_power(x R: x >= 0) R = x^(1/2)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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

forall a N_pos, n N:
    a^n $in N_pos
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("sqrt_core_builtin_rules");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "sqrt_core_builtin_rules failed:\n{}",
            run_output
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

        let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

            let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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
    assert!(run_output.contains("\"rule\": \"div_not_equal_zero_from_numerator_nonzero\""));
}

#[test]
fn known_obj_values_store_simplified_fraction_for_nonfinite_decimal() {
    let source_code = r#"
have a R
know a = 1 / 2 / 3

have b R
know b = 1 / 2

have c R
know c = 2 / -6

have d R
know d = 1 / (2 / 3 * 4)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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

    let env = runtime.environment_stack.last().expect("top environment");
    match env.known_obj_values.get("a") {
        Some(KnownObjValue::SimplifiedFraction(div)) => {
            assert_eq!(div.left.to_string(), "1");
            assert_eq!(div.right.to_string(), "6");
        }
        other => panic!(
            "expected a to store SimplifiedFraction(1 / 6), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get("b") {
        Some(KnownObjValue::SimplifiedNumber(number)) => {
            assert_eq!(number.normalized_value, "0.5");
        }
        other => panic!(
            "expected b to store SimplifiedNumber(0.5), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get("c") {
        Some(KnownObjValue::SimplifiedFraction(div)) => {
            assert_eq!(div.left.to_string(), "-1");
            assert_eq!(div.right.to_string(), "3");
        }
        other => panic!(
            "expected c to store SimplifiedFraction(-1 / 3), got {:?}",
            other.map(|_| "other value")
        ),
    }
    match env.known_obj_values.get("d") {
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

    let mut runtime = Runtime::new_with_builtin_code();
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
have I set = oo(0, 1)

have a R
know a $in oo(0, 1)
a $in R
0 < a
a < 1

have b R
know b $in oc(0, 1)
0 < b
b <= 1

have c R
know c $in co(0, 1)
0 <= c
c < 1

have d R
know d $in cc(0, 1)
0 <= d
d <= 1

have e R
know e $in info(1)
e $in R
e < 1

have f R
know f $in infc(1)
f $in R
f <= 1

have g R
know g $in oinf(0)
g $in R
0 < g

have h R
know h $in cinf(0)
h $in R
0 <= h

have x R
know:
    0 < x
    x <= 1
x $in oc(0, 1)

have y R
know:
    0 <= y
y $in cinf(0)

have phi fn(t oo(0, 1)) R
phi(a) $in R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
fn real_interval_nonempty_and_well_defined_rules() {
    let source_code = r#"
have empty_like set = cc(1, 0)

have a, b R
know:
    a <= b
    a < b

$is_nonempty_set(cc(a, b))
$is_nonempty_set(oo(a, b))
$is_nonempty_set(oc(a, b))
$is_nonempty_set(co(a, b))
$is_nonempty_set(info(a))
$is_nonempty_set(infc(a))
$is_nonempty_set(oinf(a))
$is_nonempty_set(cinf(a))

have x cc(a, b)
x $in cc(a, b)

have y oo(a, b)
y $in oo(a, b)

have left cinf(a)
left $in cinf(a)

have right info(a)
right $in info(a)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
fn common_power_equalities_and_order_are_builtin() {
    run_with_large_stack("common_power_equalities_and_order_are_builtin", || {
        let source_code = r#"
forall x Q, n, m N:
    x^n * x^m = x^(n + m)

forall x, y Q, n N:
    (x * y)^n = x^n * y^n

forall x Q, n N_pos:
    x^n = 0
    =>:
        x = 0

forall x, y Q, n N_pos:
    x >= y
    y >= 0
    =>:
        x^n >= y^n
        y^n >= 0

forall x Q, n N_pos:
    abs(x^n) = abs(x)^n

forall x Q_nz, n, m Z:
    x^n * x^m = x^(n + m)

8^(1/3) = 2
"#;

        let mut runtime = Runtime::new_with_builtin_code();
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
        assert!(run_output.contains("equality: x^(1/n) = z from x = z^n, n in N_pos, and z >= 0"));
    });
}

#[test]
fn reciprocal_power_root_rule_rejects_negative_even_root() {
    run_with_large_stack(
        "reciprocal_power_root_rule_rejects_negative_even_root",
        || {
            let source_code = r#"
16^(1/2) = -4
"#;

            let mut runtime = Runtime::new_with_builtin_code();
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
know:
    $is_nonempty_set(A)

$is_nonempty_set(union(A, B))

have C, D set
know:
    $is_nonempty_set(D)

$is_nonempty_set(union(C, D))
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
fn union_set_equalities_are_builtin() {
    let source_code = r#"
forall A, B set:
    union(A, B) = union(B, A)

forall A, B, C set:
    union(union(A, B), C) = union(A, union(B, C))

forall A set:
    union(A, A) = A
    union(A, {}) = A
    union({}, A) = A

have A, B, C set
union(A, B) = union(B, A)
union(union(A, B), C) = union(A, union(B, C))
union(A, union(B, C)) = union(union(A, B), C)
union(A, A) = A
union(A, {}) = A
union({}, A) = A
A = union(A, A)
A = union(A, {})
A = union({}, A)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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

forall A, B, C set:
    intersect(intersect(A, B), C) = intersect(A, intersect(B, C))

forall A, B, C set:
    intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))

forall A, B, C set:
    set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))

forall A, B, C set:
    set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))

have A, B, C set
intersect(A, B) = intersect(B, A)
intersect(intersect(A, B), C) = intersect(A, intersect(B, C))
intersect(A, intersect(B, C)) = intersect(intersect(A, B), C)
intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))
union(intersect(A, B), intersect(A, C)) = intersect(A, union(B, C))
set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))
intersect(set_minus(A, B), set_minus(A, C)) = set_minus(A, union(B, C))
set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))
union(set_minus(A, B), set_minus(A, C)) = set_minus(A, intersect(B, C))
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("common_set_algebra_equalities_are_builtin");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "common_set_algebra_equalities_are_builtin failed:\n{}",
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
    ];

    for (i, source_code) in cases.iter().enumerate() {
        let mut runtime = Runtime::new_with_builtin_code();
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
fn one_side_infinity_interval_parse_arity_errors() {
    for source_code in ["have bad set = info()", "have bad set = info(0, 1)"] {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("one_side_infinity_interval_parse_arity_errors");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(!run_succeeded);
        assert!(
            run_output.contains("info expects 1 argument"),
            "unexpected arity error output:\n{}",
            run_output
        );
    }
}

#[test]
#[ignore = "std run_file was removed; import currently registers modules without executing them"]
fn typed_function_applications_return_real() {
    let source_code = r#"
run_file Trig

sin(0) $in R
cos(pi / 3) $in R
arcsin(1 / 2) $in R
arctan(sqrt(3)) $in R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("typed_function_applications_return_real");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "typed_function_applications_return_real failed:\n{}",
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

    let mut runtime = Runtime::new_with_builtin_code();
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

    let mut runtime = Runtime::new_with_builtin_code();
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
fn template_can_use_struct_with_function_valued_fields() {
    let source_code = r#"
prop GroupProperty(s set, inv fn(x s) s, op fn(x, y s) s, e s):
    forall x, y, z s:
        op(x, op(y, z)) = op(op(x, y), z)
    forall x s:
        op(e, x) = x
        op(x, e) = x
    forall x s:
        op(x, inv(x)) = e
        op(inv(x), x) = e

struct Group<s set>:
    inv fn(x s) s
    op fn(x, y s) s
    e s
    <=>:
        $GroupProperty(s, inv, op, e)

template<s set>:
    have group_quotient fn (g &Group<s>) power_set(s)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
}

#[test]
fn set_alias_to_fn_set_is_nonempty_and_registers_function_type() {
    let source_code = r#"
have T set = fn(i closed_range(1, 3), j closed_range(1, 3), k closed_range(1, 3)) R
have A T
A(1, 2, 3) $in R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
    have tensor3 set = fn(i closed_range(1, n), j closed_range(1, n), k closed_range(1, n)) S

have A \tensor3<R, 3>
A(1, 2, 3) $in R
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
know a <= b
a = b
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
fn zero_product_cancellation_does_not_recursively_reenter_equality() {
    let source_code = r#"
have a, b, k1, k2 N
know:
    k1 = 0
    b = a * k1
b = a * k1 = a * 0 = 0
0 * k2 = 0
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
know exist! a, b R st {$p(a, b)}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("exist_unique_infers_component_uniqueness_forall");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "exist! component uniqueness inference failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("forall a1, b1 R, a2, b2 R:")
            && run_output.contains("a1 = a2 and b1 = b2"),
        "exist! should infer a component-wise uniqueness forall:\n{}",
        run_output
    );
}

#[test]
fn exist_unique_component_uniqueness_proves_split_then_facts() {
    let source_code = r#"
abstract_prop p(a, b)
know exist! a, b R st {$p(a, b)}
forall a1, b1, a2, b2 R:
    $p(a1, b1)
    $p(a2, b2)
    =>:
        a1 = a2
        b1 = b2
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
    know:
        exist a, b R st {$p(a, b)}
        forall a1, b1, a2, b2 R:
            $p(a1, b1)
            $p(a2, b2)
            =>:
                (a1, b1) = (a2, b2)
    exist! a, b R st {$p(a, b)}
"#;

    let mut runtime = Runtime::new_with_builtin_code();
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
fn have_fn_as_set_accepts_prove_block_target() {
    let source_code = r#"
abstract_prop F(x, y)
have A set
have B set
know forall x A:
    exist! y B st {$F(x, y)}

have fn f as set:
    prove:
        forall x A:
            exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("have_fn_as_set_accepts_prove_block_target");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "have fn as set prove target should succeed:\n{}",
        run_output
    );
}

#[test]
fn have_fn_as_set_prove_body_can_establish_target() {
    let source_code = r#"
abstract_prop F(x, y)
have A set
have B set

have fn f as set:
    prove:
        forall x A:
            exist! y B st {$F(x, y)}
    know exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("have_fn_as_set_prove_body_can_establish_target");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "have fn as set proof body should establish the target forall:\n{}",
        run_output
    );
}

#[test]
fn have_fn_as_set_still_accepts_direct_forall_compatibility_form() {
    let source_code = r#"
abstract_prop F(x, y)
have A set
have B set
know forall x A:
    exist! y B st {$F(x, y)}

have fn f as set:
    forall x A:
        exist! y B st {$F(x, y)}

forall x A:
    $F(x, f(x))
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "have_fn_as_set_still_accepts_direct_forall_compatibility_form",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "legacy direct forall form should remain accepted:\n{}",
        run_output
    );
}

#[test]
fn have_fn_as_set_prove_block_requires_forall_target() {
    let source_code = r#"
have fn f as set:
    prove:
        1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("have_fn_as_set_prove_block_requires_forall_target");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "non-forall prove target should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("`prove:` must contain a single `forall` fact"),
        "non-forall prove target should report the expected shape:\n{}",
        run_output
    );
}

#[test]
fn hidden_file_path_output_omits_source_fields() {
    let source_code = "x = 1";
    let path = "/private/tmp/litex-hidden-source-test.lit";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(path);
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(!run_output.contains("\"source\""));
    assert!(!run_output.contains(path));
    assert!(run_output.contains("\"line\": 1"));
}

#[test]
fn normal_output_omits_empty_arrays_and_empty_strings() {
    let source_code = "do_nothing\nhave a R\nhave a R";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("normal_output_omits_empty_fields");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(!run_output.contains("\"store_facts\": []"));
    assert!(!run_output.contains("\"inside_results\": []"));
    assert!(!run_output.contains("\"message\": \"\""));
}

#[test]
fn detail_output_keeps_empty_arrays_and_empty_strings() {
    let source_code = "do_nothing\nhave a R\nhave a R";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("detail_output_keeps_empty_fields");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(!run_output.contains("\"store_facts\": []"));
    assert!(!run_output.contains("\"inside_results\": []"));
    assert!(!run_output.contains("\"message\": \"\""));
}

#[test]
fn normal_output_folds_proof_level_inside_results() {
    run_with_large_stack("normal_output_folds_proof_level_inside_results", || {
        let source_code = r#"
sketch:
    1 = 1

claim:
    prove:
        1 = 1
    1 = 1

by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1

witness exist x R st {x = 1} from 1:
    1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("normal_output_folds_proof_trace");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "normal proof-trace fixture failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"type\": \"proof sketch\""));
        assert!(run_output.contains("\"type\": \"proved claim\""));
        assert!(run_output.contains("\"type\": \"proof by cases\""));
        assert!(run_output.contains("\"type\": \"existence witness\""));
        assert_no_legacy_acceptance_field(&run_output, "normal");
        assert!(
            !run_output.contains("\"inside_results\": ["),
            "normal output should fold raw recursive inside_results:\n{}",
            run_output
        );
    });
}

#[test]
fn detail_output_expands_proof_level_inside_results() {
    run_with_large_stack("detail_output_expands_proof_level_inside_results", || {
        let source_code = r#"
sketch:
    1 = 1

claim:
    prove:
        1 = 1
    1 = 1

by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1

witness exist x R st {x = 1} from 1:
    1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("detail_output_expands_proof_trace");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "detail proof-trace fixture failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"type\": \"proof sketch\""));
        assert!(run_output.contains("\"type\": \"proved claim\""));
        assert!(run_output.contains("\"type\": \"proof by cases\""));
        assert!(run_output.contains("\"type\": \"existence witness\""));
        assert!(
            run_output.matches("\"inside_results\": [").count() >= 3,
            "detail output should expand available raw recursive inside_results:\n{}",
            run_output
        );
    });
}

#[test]
fn by_induc_output_uses_same_trace_for_normal_and_detail() {
    let source_code = r#"
abstract_prop p(a)
know $p(0)
know forall m Z:
    m >= 0
    $p(m)
    =>:
        $p(m + 1)
by induc n from 0:
    prove:
        $p(n)

    prove from n = 0:
        $p(0)

    prove induc:
        $p(n + 1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("by_induc_normal_trace");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "normal by induc fixture failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"proof by induction\""));
    assert!(
        !run_output.contains("\"inside_results\": ["),
        "normal by induc output should fold raw inside_results:\n{}",
        run_output
    );

    let mut detail_runtime = Runtime::new_with_builtin_code();
    detail_runtime.new_file_path_new_env_new_name_scope("by_induc_detail_trace");
    detail_runtime.detail_output = true;
    let (detail_stmt_results, detail_runtime_error) =
        run_source_code(source_code, &mut detail_runtime);
    let (detail_run_succeeded, detail_run_output) = render_run_source_code_output(
        &detail_runtime,
        &detail_stmt_results,
        &detail_runtime_error,
        false,
    );

    assert!(
        detail_run_succeeded,
        "detail by induc fixture failed:\n{}",
        detail_run_output
    );
    assert!(detail_run_output.contains("\"type\": \"proof by induction\""));
    assert!(detail_run_output.contains("\"inside_results\": ["));
    assert!(detail_run_output.contains("\"statement\": \"$p(0)\""));
    assert!(
        detail_run_output.matches("\"type\": \"prop fact\"").count() >= 4,
        "detail by induc output should expand base/step proof and obligation checks:\n{}",
        detail_run_output
    );
    assert!(detail_run_output.contains("+ 1)"));
}

#[test]
fn witness_detail_output_keeps_proof_and_obligation_trace() {
    let source_code = r#"
witness exist x R st {x = 1} from 1:
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("witness_detail_output_keeps_trace");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "witness detail fixture failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"existence witness\""));
    assert!(
        run_output.matches("\"statement\": \"1 = 1\"").count() >= 2,
        "witness detail output should include the proof step and the instantiated obligation:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"inside_results\": ["),
        "witness detail output should expand its proof trace:\n{}",
        run_output
    );
}

#[test]
fn builtin_citation_source_uses_safe_builtin_label() {
    let source_code = "have a, b R\na < b or a = b or a > b";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("builtin_citation_source");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "builtin citation run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"source_kind\": \"builtin\""));
    assert!(run_output.contains("\"source\": \"builtin_code\""));
    assert!(!run_output.contains("\"path\""));
}

#[test]
#[ignore = "std run_file was removed; import currently registers modules without executing them"]
fn std_citation_source_uses_safe_module_label() {
    let source_code = "run_file Trig\nsin(0) = 0";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("std_citation_source");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(run_succeeded, "std citation run failed:\n{}", run_output);
    assert!(run_output.contains("\"source_kind\": \"std\""));
    assert!(run_output.contains("\"source\": \"std/Trig\""));
    assert!(!run_output.contains("\"path\""));
}

#[test]
fn run_file_citation_source_uses_safe_label_and_detail_path() {
    let run_file_path = std::env::temp_dir().join("litex-run-file-citation-source-test.lit");
    fs::write(
        &run_file_path,
        "abstract_prop p(x)\nknow forall x R:\n    $p(x)\n",
    )
    .unwrap();
    let run_file_path_string = run_file_path.to_string_lossy().into_owned();
    let source_code = format!("run_file \"{}\"\n$p(2)", run_file_path_string);

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("run_file_citation_source");
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "run_file citation run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"source_kind\": \"run_file\""));
    assert!(run_output.contains("\"source\": \"external_file\""));
    assert!(!run_output.contains(run_file_path_string.as_str()));

    let mut detail_runtime = Runtime::new_with_builtin_code();
    detail_runtime.new_file_path_new_env_new_name_scope("run_file_citation_source");
    detail_runtime.detail_output = true;
    let (detail_stmt_results, detail_runtime_error) =
        run_source_code(source_code.as_str(), &mut detail_runtime);
    let (detail_run_succeeded, detail_run_output) = render_run_source_code_output(
        &detail_runtime,
        &detail_stmt_results,
        &detail_runtime_error,
        false,
    );

    let _ = fs::remove_file(&run_file_path);
    assert!(
        detail_run_succeeded,
        "detail run_file citation run failed:\n{}",
        detail_run_output
    );
    assert!(detail_run_output.contains("\"path\""));
    assert!(detail_run_output.contains(run_file_path_string.as_str()));
}

#[test]
fn runner_success_returns_trace() {
    let (ok, output) = run_runner_for_code("1 + 1 = 2", "-runner-test", true);

    assert!(ok, "runner success run failed:\n{}", output);
    assert!(output.contains("\"runner\": \"litex-runner\""));
    assert!(output.contains("\"result\": \"success\""));
    assert!(output.contains("\"trace\""));
}

#[test]
fn runner_failure_returns_trace() {
    let (ok, output) = run_runner_for_code("1 = 0", "-runner-test", true);

    assert!(!ok, "runner unknown run should fail:\n{}", output);
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains("\\\"error_type\\\": \\\"VerifyError\\\""));
    assert!(output.contains("\\\"error_type\\\": \\\"UnknownError\\\""));
}

#[test]
fn runner_target_error_returns_message() {
    let (ok, output) = run_runner_for_file("does_not_exist.lit", true);

    assert!(!ok, "runner target error should fail:\n{}", output);
    assert!(output.contains("\"kind\": \"target_error\""));
    assert!(output.contains("could not read entry file"));
}

#[test]
fn runner_accepts_know_as_normal_execution() {
    let (ok, output) = run_runner_for_code("know 1 = 0", "-runner-test", true);

    assert!(ok, "runner should not reject know statements:\n{}", output);
    assert!(output.contains("\"result\": \"success\""));
}

#[test]
fn runner_accepts_let_as_normal_execution() {
    let (ok, output) = run_runner_for_code("let x R", "-runner-test", true);

    assert!(ok, "runner should not reject let statements:\n{}", output);
    assert!(output.contains("\"result\": \"success\""));
}

#[test]
fn zh_output_localizes_unproved_know_labels() {
    let source_code = "abstract_prop tmp_rel(m, n)\nknow exist! m, n R st {$tmp_rel(m, n)}\n";
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("zh_output_localizes_unproved_know_labels");
    runtime.output_language = OutputLanguage::SimplifiedChinese;

    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(run_succeeded, "Chinese output run failed:\n{}", run_output);
    assert!(run_output.contains("\"结果\": \"成功\""));
    assert!(run_output.contains("\"类型\": \"未经证明的假设\""));
    assert!(run_output.contains("\"原因\": \"警告：未经证明的 know 假设\""));
    assert!(run_output.contains("\"事实\": \"exist! m, n R st {$tmp_rel("));
    assert!(!run_output.contains("\"result\": \"success\""));
}

#[test]
fn zh_output_localizes_citation_evidence_but_keeps_litex_statement() {
    let source_code = "prop is_one_tmp(t R):\n    t = 1\n\n$is_one_tmp(1)\n";
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "zh_output_localizes_citation_evidence_but_keeps_litex_statement",
    );
    runtime.output_language = OutputLanguage::SimplifiedChinese;

    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "Chinese citation run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"验证\""));
    assert!(run_output.contains("\"类型\": \"引用 prop 定义\""));
    assert!(run_output.contains("\"被引用语句\": \"prop is_one_tmp(t R):\\n"));
    assert!(run_output.contains("\"语句\": \"$is_one_tmp(1)\""));
}

#[test]
fn zh_forall_output_uses_short_conclusions_and_compact_citation() {
    let source_code = r#"
have human nonempty_set, Socrates human
abstract_prop mortal(x)

forall:
    forall x human:
        $mortal(x)
    =>:
        $mortal(Socrates)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "zh_forall_output_uses_short_conclusions_and_compact_citation",
    );
    runtime.output_language = OutputLanguage::SimplifiedChinese;

    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "Chinese forall output run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"结论\": ["));
    assert!(run_output.contains("\"类型\": \"引用 forall 事实\""));
    assert!(run_output.contains("\"被引用语句\": \"forall x human:\\n    $mortal(x)\""));
    assert!(run_output.contains("\"原因\": \"已证明语句\""));
    assert!(!run_output.contains("\"带验证的结论\""));
    assert!(!run_output.contains("\"原因\": \"推导事实\""));
    assert!(!run_output.contains("\"实例化\""));
    assert!(!run_output.contains("\"要求\""));
}

#[test]
fn zh_runner_localizes_wrapper_and_trace() {
    let (ok, output) = run_runner_for_code_with_language(
        "know 1 = 1",
        "-runner-test",
        true,
        OutputLanguage::SimplifiedChinese,
    );

    assert!(ok, "Chinese runner should succeed:\n{}", output);
    assert!(output.contains("\"运行器\": \"litex-runner\""));
    assert!(output.contains("\"结果\": \"成功\""));
    assert!(output.contains("\"运行轨迹\""));
    assert!(output.contains("\\\"类型\\\": \\\"未经证明的假设\\\""));
}

#[test]
fn output_language_parses_supported_cli_codes() {
    let cases = vec![
        ("en", OutputLanguage::English),
        ("zh", OutputLanguage::SimplifiedChinese),
        ("zh-Hans", OutputLanguage::TraditionalChinese),
        ("ja", OutputLanguage::Japanese),
        ("ko", OutputLanguage::Korean),
        ("es", OutputLanguage::Spanish),
        ("fr", OutputLanguage::French),
        ("de", OutputLanguage::German),
        ("pt", OutputLanguage::Portuguese),
        ("ru", OutputLanguage::Russian),
        ("ar", OutputLanguage::Arabic),
        ("hi", OutputLanguage::Hindi),
        ("vi", OutputLanguage::Vietnamese),
        ("id", OutputLanguage::Indonesian),
    ];

    for (code, expected) in cases {
        assert_eq!(OutputLanguage::from_cli_lang(code), Ok(expected));
    }

    let err = OutputLanguage::from_cli_lang("xx").expect_err("xx should be unsupported");
    assert!(err.contains("en, zh, zh-Hans, ja, ko, es, fr, de, pt, ru, ar, hi, vi, id"));
}

#[test]
fn non_english_languages_localize_unproved_know_labels() {
    let cases = vec![
        (
            OutputLanguage::SimplifiedChinese,
            "结果",
            "成功",
            "类型",
            "未经证明的假设",
            "语句",
            "事实",
            "原因",
            "警告：未经证明的 know 假设",
        ),
        (
            OutputLanguage::TraditionalChinese,
            "結果",
            "成功",
            "類型",
            "未經證明的假設",
            "語句",
            "事實",
            "原因",
            "警告：未經證明的 know 假設",
        ),
        (
            OutputLanguage::Japanese,
            "結果",
            "成功",
            "種類",
            "証明されていない仮定",
            "文",
            "事実",
            "理由",
            "警告：証明されていない know 仮定",
        ),
        (
            OutputLanguage::Korean,
            "결과",
            "성공",
            "유형",
            "증명되지 않은 가정",
            "문장",
            "사실",
            "이유",
            "경고: 증명되지 않은 know 가정",
        ),
        (
            OutputLanguage::Spanish,
            "resultado",
            "éxito",
            "tipo",
            "suposición no demostrada",
            "enunciado",
            "hecho",
            "razón",
            "advertencia: suposición know no demostrada",
        ),
        (
            OutputLanguage::French,
            "résultat",
            "succès",
            "type",
            "hypothèse non prouvée",
            "énoncé",
            "fait",
            "raison",
            "avertissement : hypothèse know non prouvée",
        ),
        (
            OutputLanguage::German,
            "Ergebnis",
            "Erfolg",
            "Typ",
            "unbewiesene Annahme",
            "Anweisung",
            "Fakt",
            "Grund",
            "Warnung: unbewiesene know-Annahme",
        ),
        (
            OutputLanguage::Portuguese,
            "resultado",
            "sucesso",
            "tipo",
            "suposição não provada",
            "declaração",
            "fato",
            "razão",
            "aviso: suposição know não provada",
        ),
        (
            OutputLanguage::Russian,
            "результат",
            "успех",
            "тип",
            "недоказанное предположение",
            "утверждение",
            "факт",
            "причина",
            "предупреждение: недоказанное предположение know",
        ),
        (
            OutputLanguage::Arabic,
            "النتيجة",
            "نجاح",
            "النوع",
            "افتراض غير مبرهن",
            "العبارة",
            "الحقيقة",
            "السبب",
            "تحذير: افتراض know غير مبرهن",
        ),
        (
            OutputLanguage::Hindi,
            "परिणाम",
            "सफलता",
            "प्रकार",
            "अप्रमाणित मान्यता",
            "कथन",
            "तथ्य",
            "कारण",
            "चेतावनी: अप्रमाणित know मान्यता",
        ),
        (
            OutputLanguage::Vietnamese,
            "kết_quả",
            "thành công",
            "kiểu",
            "giả thiết chưa chứng minh",
            "mệnh_đề",
            "sự_kiện",
            "lý_do",
            "cảnh báo: giả thiết know chưa chứng minh",
        ),
        (
            OutputLanguage::Indonesian,
            "hasil",
            "sukses",
            "tipe",
            "asumsi belum terbukti",
            "pernyataan",
            "fakta",
            "alasan",
            "peringatan: asumsi know belum terbukti",
        ),
    ];

    for (
        language,
        result_key,
        success_text,
        type_key,
        type_text,
        statement_key,
        fact_key,
        reason_key,
        reason_text,
    ) in cases
    {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "non_english_languages_localize_unproved_know_labels",
        );
        runtime.output_language = language;

        let (stmt_results, runtime_error) = run_source_code("know 1 = 1", &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "localized output run failed:\n{}",
            run_output
        );
        assert!(run_output.contains(&format!("\"{}\": \"{}\"", result_key, success_text)));
        assert!(run_output.contains(&format!("\"{}\": \"{}\"", type_key, type_text)));
        assert!(run_output.contains(&format!("\"{}\": \"know 1 = 1\"", statement_key)));
        assert!(run_output.contains(&format!("\"{}\": \"1 = 1\"", fact_key)));
        assert!(run_output.contains(&format!("\"{}\": \"{}\"", reason_key, reason_text)));
        assert!(!run_output.contains("\"result\": \"success\""));
    }
}

#[test]
fn non_english_runner_localizes_wrapper_keys() {
    let cases = vec![
        (
            OutputLanguage::SimplifiedChinese,
            "运行器",
            "结果",
            "成功",
            "是否成功",
            "运行目标",
            "运行轨迹",
        ),
        (
            OutputLanguage::TraditionalChinese,
            "執行器",
            "結果",
            "成功",
            "是否成功",
            "目標",
            "執行追蹤",
        ),
        (
            OutputLanguage::Japanese,
            "ランナー",
            "結果",
            "成功",
            "成功",
            "対象",
            "実行トレース",
        ),
        (
            OutputLanguage::Korean,
            "러너",
            "결과",
            "성공",
            "성공 여부",
            "대상",
            "실행 추적",
        ),
        (
            OutputLanguage::Spanish,
            "ejecutor",
            "resultado",
            "éxito",
            "correcto",
            "objetivo",
            "traza",
        ),
        (
            OutputLanguage::French,
            "exécuteur",
            "résultat",
            "succès",
            "réussi",
            "cible",
            "trace",
        ),
        (
            OutputLanguage::German,
            "Runner",
            "Ergebnis",
            "Erfolg",
            "erfolgreich",
            "Ziel",
            "Ablaufspur",
        ),
        (
            OutputLanguage::Portuguese,
            "executor",
            "resultado",
            "sucesso",
            "bem_sucedido",
            "alvo",
            "rastreamento",
        ),
        (
            OutputLanguage::Russian,
            "запускатель",
            "результат",
            "успех",
            "успешно",
            "цель",
            "трасса",
        ),
        (
            OutputLanguage::Arabic,
            "المشغل",
            "النتيجة",
            "نجاح",
            "ناجح",
            "الهدف",
            "الأثر",
        ),
        (
            OutputLanguage::Hindi,
            "रनर",
            "परिणाम",
            "सफलता",
            "सफल",
            "लक्ष्य",
            "चलन_चिह्न",
        ),
        (
            OutputLanguage::Vietnamese,
            "trình_chạy",
            "kết_quả",
            "thành công",
            "đúng",
            "mục_tiêu",
            "vết_chạy",
        ),
        (
            OutputLanguage::Indonesian,
            "runner",
            "hasil",
            "sukses",
            "berhasil",
            "target",
            "jejak",
        ),
    ];

    for (language, runner_key, result_key, success_text, ok_key, target_key, trace_key) in cases {
        let (ok, output) =
            run_runner_for_code_with_language("know 1 = 1", "-runner-test", true, language);

        assert!(ok, "localized runner should succeed:\n{}", output);
        assert!(output.contains(&format!("\"{}\": \"litex-runner\"", runner_key)));
        assert!(output.contains(&format!("\"{}\": \"{}\"", result_key, success_text)));
        assert!(output.contains(&format!("\"{}\": true", ok_key)));
        assert!(output.contains(&format!("\"{}\"", target_key)));
        assert!(output.contains(&format!("\"{}\"", trace_key)));
        assert!(!output.contains("\"result\": \"success\""));
    }
}

#[test]
fn strict_mode_rejects_user_know() {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_rejects_user_know");
    runtime.strict_mode = true;

    let (stmt_results, runtime_error) = run_source_code("know 1 = 0", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "strict mode should reject user know statements:\n{}",
        run_output
    );
    assert!(
        run_output.contains(KnowStmt::strict_mode_rejection_message()),
        "strict mode should report the know boundary:\n{}",
        run_output
    );
}

#[test]
fn strict_mode_rejects_user_let() {
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_rejects_user_let");
    runtime.strict_mode = true;

    let (stmt_results, runtime_error) = run_source_code("let x R", &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "strict mode should reject user let statements:\n{}",
        run_output
    );
    assert!(
        run_output.contains(DefLetStmt::strict_mode_rejection_message()),
        "strict mode should report the let boundary:\n{}",
        run_output
    );
}

#[test]
fn strict_runner_rejects_user_know() {
    let (ok, output) = run_runner_for_code_strict("know 1 = 0", "-runner-test", true);

    assert!(
        !ok,
        "strict runner should reject know statements:\n{}",
        output
    );
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains(KnowStmt::strict_mode_rejection_message()));
}

#[test]
fn strict_runner_rejects_user_let() {
    let (ok, output) = run_runner_for_code_strict("let x R", "-runner-test", true);

    assert!(
        !ok,
        "strict runner should reject let statements:\n{}",
        output
    );
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains(DefLetStmt::strict_mode_rejection_message()));
}

#[test]
fn strict_mode_allows_imported_module_know() {
    let module_dir =
        std::env::temp_dir().join(format!("litex-strict-import-{}", std::process::id()));
    fs::create_dir_all(&module_dir).expect("create strict import test module");
    fs::write(
        module_dir.join("main.lit"),
        "abstract_prop imported_prop(x)\nknow $imported_prop(2)\n",
    )
    .expect("write strict import test module");
    let source_code = format!(
        "import \"{}\" as Trusted\n$Trusted::imported_prop(2)",
        module_dir.to_string_lossy()
    );

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_allows_imported_module_know");
    runtime.strict_mode = true;
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    let _ = fs::remove_dir_all(&module_dir);
    assert!(
        run_succeeded,
        "strict mode should allow know inside imported modules:\n{}",
        run_output
    );
}

#[test]
fn strict_mode_allows_imported_module_let() {
    let module_dir =
        std::env::temp_dir().join(format!("litex-strict-import-let-{}", std::process::id()));
    fs::create_dir_all(&module_dir).expect("create strict import let test module");
    fs::write(module_dir.join("main.lit"), "let imported_value R\n")
        .expect("write strict import let test module");
    let source_code = format!("import \"{}\" as Trusted", module_dir.to_string_lossy());

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_allows_imported_module_let");
    runtime.strict_mode = true;
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    let _ = fs::remove_dir_all(&module_dir);
    assert!(
        run_succeeded,
        "strict mode should allow let inside imported modules:\n{}",
        run_output
    );
}

#[test]
fn strict_mode_rejects_run_file_know() {
    let run_file_path =
        std::env::temp_dir().join(format!("litex-strict-run-file-{}.lit", std::process::id()));
    fs::write(&run_file_path, "know 1 = 0\n").expect("write strict run_file test file");
    let source_code = format!("run_file \"{}\"", run_file_path.to_string_lossy());

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_rejects_run_file_know");
    runtime.strict_mode = true;
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    let _ = fs::remove_file(&run_file_path);
    assert!(
        !run_succeeded,
        "strict mode should reject know inside run_file:\n{}",
        run_output
    );
    assert!(
        run_output.contains(KnowStmt::strict_mode_rejection_message()),
        "strict run_file failure should report the know boundary:\n{}",
        run_output
    );
}

#[test]
fn strict_mode_rejects_run_file_let() {
    let run_file_path = std::env::temp_dir().join(format!(
        "litex-strict-run-file-let-{}.lit",
        std::process::id()
    ));
    fs::write(&run_file_path, "let x R\n").expect("write strict run_file let test file");
    let source_code = format!("run_file \"{}\"", run_file_path.to_string_lossy());

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("strict_mode_rejects_run_file_let");
    runtime.strict_mode = true;
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    let _ = fs::remove_file(&run_file_path);
    assert!(
        !run_succeeded,
        "strict mode should reject let inside run_file:\n{}",
        run_output
    );
    assert!(
        run_output.contains(DefLetStmt::strict_mode_rejection_message()),
        "strict run_file failure should report the let boundary:\n{}",
        run_output
    );
}

#[test]
fn hidden_file_path_run_file_output_omits_run_file_path() {
    let run_file_path = std::env::temp_dir().join("litex-hidden-run-file-test.lit");
    fs::write(&run_file_path, "1 = 1\n").unwrap();
    let run_file_path_string = run_file_path.to_string_lossy().into_owned();
    let source_code = format!("run_file \"{}\"", run_file_path_string);

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("repl");
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    let _ = fs::remove_file(&run_file_path);
    assert!(run_succeeded, "run_file failed:\n{}", run_output);
    assert!(run_output.contains("\"statement\": \"run_file"));
    assert!(!run_output.contains(run_file_path_string.as_str()));
    assert!(!run_output.contains("\"source\""));
}

#[test]
fn run_file_read_error_hides_path_unless_detail_output() {
    let run_file_path = std::env::temp_dir().join("litex-missing-run-file-output-test.lit");
    let _ = fs::remove_file(&run_file_path);
    let run_file_path_string = run_file_path.to_string_lossy().into_owned();
    let source_code = format!("run_file \"{}\"", run_file_path_string);

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("repl");
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(run_output.contains("Failed to read file: external_file"));
    assert!(!run_output.contains(run_file_path_string.as_str()));

    let mut detail_runtime = Runtime::new_with_builtin_code();
    detail_runtime.new_file_path_new_env_new_name_scope("repl");
    detail_runtime.detail_output = true;
    let (detail_stmt_results, detail_runtime_error) =
        run_source_code(source_code.as_str(), &mut detail_runtime);
    let (detail_run_succeeded, detail_run_output) = render_run_source_code_output(
        &detail_runtime,
        &detail_stmt_results,
        &detail_runtime_error,
        false,
    );

    assert!(!detail_run_succeeded);
    assert!(detail_run_output.contains(run_file_path_string.as_str()));
}

#[test]
fn unquoted_run_file_is_rejected() {
    let source_code = "run_file Trig";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("repl");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(run_output.contains(
        "run_file expects a quoted relative or absolute file path; use import <std_module> for std modules"
    ));
}

#[test]
fn citation_verified_by_type_reflects_cited_stmt_kind() {
    let source_code = r#"
abstract_prop p(x)
know forall x R:
    $p(x)
$p(2)
let a R:
    a = 1
a = 1
prop q(x R):
    x = 1
$q(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("citation_verified_by_type_reflects_cited_stmt_kind");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "citation_verified_by_type_reflects_cited_stmt_kind failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"cite forall fact\""));
    assert!(!run_output.contains("\"instantiation\""));
    assert!(!run_output.contains("\"requirements\""));
    assert!(!run_output.contains("\"statement\": \"2 $in R\""));
    assert!(run_output.contains("\"type\": \"cite equality fact\""));
    assert!(run_output.contains("\"type\": \"cite prop def\""));
}

#[test]
fn factual_verification_uses_stable_object_shape() {
    let source_code = r#"
1 = 1
forall x R:
    x = x
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("factual_verified_by_stable_shape");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "factual_verified_by_stable_shape failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"verification\": {\n    \"type\": \"builtin rule\""),
        "builtin fact should render verification as an object:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"summary\": \"conclusions verified under forall assumptions\""),
        "forall fact should not render a separate top-level verification summary:\n{}",
        run_output
    );
    assert!(run_output.contains("\"parameters\": ["));
    assert!(run_output.contains("\"assumptions\": ["));
    assert!(
        !run_output.contains("\"verified_by\""),
        "public output should use verification instead of verified_by:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"conclusions\": ["),
        "forall proof should keep one verification entry per then fact:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"verification\": {"),
        "forall proof conclusions should carry their own verification objects:\n{}",
        run_output
    );
}

#[test]
fn atomic_fact_verification_output_omits_method_and_reports_route_types() {
    let source_code = r#"
1 = 1

abstract_prop known_p(x)
know $known_p(1)
$known_p(1)

abstract_prop forall_p(x)
know:
    forall x R:
        x = 1
        =>:
            $forall_p(x)
$forall_p(1)

prop def_p(x R):
    x = 1
$def_p(1)

prop sym_p(x set, y set):
    x = y
by symmetric_prop:
    prove:
        forall x, y set:
            $sym_p(x, y)
            =>:
                $sym_p(y, x)
    x = y
    y = x
have A set
have B set
know $sym_p(A, B)
$sym_p(B, A)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "atomic_fact_verification_output_omits_method_and_reports_route_types",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "atomic verification route fixture failed:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"method\""),
        "verification output should not include redundant method field:\n{}",
        run_output
    );
    for route_type in [
        "builtin rule",
        "cite equality fact",
        "cite prop fact",
        "cite forall fact",
    ] {
        assert!(
            run_output.contains(&format!("\"type\": \"{}\"", route_type)),
            "missing atomic verification route type `{}`:\n{}",
            route_type,
            run_output
        );
    }
}

#[test]
fn builtin_rule_subgoals_are_nested_under_chain_step() {
    let source_code = r#"
forall x R_pos:
    x^3 = 8
    =>:
        3 = log(2, 8) = log(2, x^3) = 3 * log(2, x)
        log(2, x) = 1
        x = 2^1 = 2
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("builtin_rule_subgoals_are_nested");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "builtin subgoal fixture failed:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"statement\": \"x = 2 ^ 1 = 2\""),
        "chain conclusion should use the public statement key:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"fact\": \"x = 2 ^ 1\""),
        "outer chain steps should include the proved chain segment:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"subgoals\": ["),
        "builtin-rule premises should be nested as subgoals:\n{}",
        run_output
    );
    assert_eq!(
        run_output.matches("\"subgoals\": [").count(),
        2,
        "normal output should show only nontrivial builtin-rule proof premises:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"statement\": \"2 ^ 3 = 8\""),
        "log(a,b)=c should expose the a^c=b proof premise:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"statement\": \"1 = log (2, x)\""),
        "the log premise should be a nested subgoal statement:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"fact\": \"1 = log (2, x)\""),
        "builtin-rule premises should not be flattened into outer chain steps:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"verified_by\""),
        "public output should use verification consistently:\n{}",
        run_output
    );
}

#[test]
fn output_store_facts_explain_context_changes() {
    let source_code = r#"
1 = 1
claim:
    prove:
        2 = 2
    2 = 2
know:
    3 = 3
let a R:
    a = a
prop q(x R):
    x = 1
$q(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("output_store_facts_explain_context_changes");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "output_store_facts_explain_context_changes failed:\n{}",
        run_output
    );
    assert!(!run_output.contains("\"infer_facts\""));
    assert!(!run_output.contains("\"effects\""));
    assert!(run_output.contains("\"store_facts\": ["));
    assert!(run_output.contains(format!("\"reason\": \"{}\"", ClaimStmt::store_reason()).as_str()));
    assert!(run_output.contains(format!("\"reason\": \"{}\"", KnowStmt::store_reason()).as_str()));
    assert!(run_output.contains(format!("\"reason\": \"{}\"", DefLetStmt::store_reason()).as_str()));
    assert!(!run_output.contains("\"trust\""));
    assert!(run_output.contains(format!("\"reason\": \"{}\"", Fact::store_reason()).as_str()));
}

#[test]
fn object_definition_output_exposes_checks_and_defined_facts() {
    run_with_large_stack(
        "object_definition_output_exposes_checks_and_defined_facts_large_stack",
        || {
            let source_code = r#"
have a R
have b R = a
have S set
know exist x R st {x = x}
have by exist x R st {x = x}: c
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "object_definition_output_exposes_checks_and_defined_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "object definition output fixture failed:\n{}",
                run_output
            );
            assert_no_legacy_acceptance_field(
                &run_output,
                HaveObjInNonemptySetOrParamTypeStmt::store_reason(),
            );
            assert!(run_output.contains("\"a $in R\""));
            assert!(run_output.contains("\"b $in R\""));
            assert!(run_output.contains("\"b = a\""));
            assert!(run_output.contains("\"$is_set(S)\""));
            assert!(run_output.contains("\"c $in R\""));
            assert!(run_output.contains("\"c = c\""));
            assert!(run_output.contains(
                format!(
                    "\"reason\": \"{}\"",
                    HaveObjInNonemptySetOrParamTypeStmt::store_reason()
                )
                .as_str()
            ));
            assert!(run_output
                .contains(format!("\"reason\": \"{}\"", HaveByExistStmt::store_reason()).as_str()));
            assert!(!run_output.contains("\"equal_to\""));
        },
    );
}

#[test]
fn forall_parameter_assumption_output_is_local_assumption() {
    let source_code = r#"
forall n N:
    n $in N
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_parameter_assumption_output");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    assert!(
        run_succeeded,
        "forall parameter assumption fixture failed:\n{}",
        run_output
    );
    assert!(!run_output.contains("\"type\": \"forall proof\""));
    assert!(run_output.contains("\"n $in N\""));
    assert!(run_output.contains("\"conclusions\": ["));
    assert!(run_output.contains("\"statement\": \"n $in N\""));
    assert!(run_output.contains("\"type\": \"local assumption\""));
    assert!(run_output
        .contains(format!("\"source\": \"{}\"", ParamDefWithType::store_reason()).as_str()));
    assert!(!run_output.contains("\"cite_source\""));
    assert!(!run_output.contains("\"verify_what\""));
    assert!(!run_output.contains("forall local check"));
}

#[test]
fn forall_output_exposes_parameters_and_assumption_store_facts() {
    run_with_large_stack(
        "forall_output_exposes_parameters_and_assumption_store_facts",
        || {
            let source_code = r#"
abstract_prop p(a, b, c)
forall a, b, c, d, e, f R:
    $p(a, b, c)
    a = d
    b = e
    c = f
    =>:
        $p(d, e, f)
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "forall_output_exposes_assumption_store_facts",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "forall assumption store-fact output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"parameters\": ["));
            assert!(run_output.contains("\"a\""));
            assert!(run_output.contains("\"f\""));
            assert!(run_output.contains("\"assumptions\": ["));
            assert!(run_output.contains("\"fact\": \"a $in R\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ParamDefWithType::store_reason()).as_str()
            ));
            assert!(run_output.contains("\"fact\": \"$p(a, b, c)\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ForallFact::premise_store_reason()).as_str()
            ));
            assert!(run_output.contains("\"fact\": \"a = d\""));
            assert!(run_output.contains("\"fact\": \"b = e\""));
            assert!(run_output.contains("\"fact\": \"c = f\""));
            assert_eq!(run_output.matches("\"fact\": \"a $in R\"").count(), 1);
        },
    );
}

#[test]
fn claim_forall_output_explains_parameters_proof_steps_and_conclusions() {
    run_with_large_stack(
        "claim_forall_output_explains_parameters_proof_steps_and_conclusions",
        || {
            let source_code = r#"
claim:
    prove:
        forall x R:
            x = 1
            =>:
                x = 1
    x = x
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("claim_forall_output_explains_proof");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

            assert!(
                run_succeeded,
                "claim forall output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proved claim\""));
            assert!(run_output.contains("\"type\": \"claim forall proof\""));
            assert!(run_output.contains("\"parameters\": ["));
            assert!(run_output.contains("\"x\""));
            assert!(run_output.contains("\"assumptions\": ["));
            assert!(run_output.contains("\"fact\": \"x $in R\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ParamDefWithType::store_reason()).as_str()
            ));
            assert!(run_output.contains("\"fact\": \"x = 1\""));
            assert!(run_output.contains(
                format!("\"reason\": \"{}\"", ForallFact::premise_store_reason()).as_str()
            ));
            assert!(run_output.contains("\"proof_steps\": ["));
            assert!(run_output.contains("\"statement\": \"x = x\""));
            assert!(run_output.contains("\"conclusions\": ["));
            assert!(run_output.contains("\"statement\": \"x = 1\""));
            assert!(run_output.contains("\"type\": \"local assumption\""));
            assert!(
                !run_output.contains("\"inside_results\": ["),
                "normal claim output should keep raw inside_results folded:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn claim_fact_output_explains_proof_steps_and_final_goal() {
    run_with_large_stack(
        "claim_fact_output_explains_proof_steps_and_final_goal",
        || {
            let source_code = r#"
claim 1 = 1:
    1 = 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("claim_fact_output_explains_goal");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "claim fact output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proved claim\""));
            assert!(run_output.contains("\"type\": \"claim proof\""));
            assert!(run_output.contains("\"prove_goal\": \"1 = 1\""));
            assert!(run_output.contains("\"proof_steps\": ["));
            assert!(run_output.contains("\"conclusion\": {"));
            assert!(run_output.contains("\"type\": \"cite equality fact\""));
            assert!(
                !run_output.contains("\"inside_results\": ["),
                "normal claim output should keep raw inside_results folded:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn output_contract_covers_composite_facts_and_control_statements() {
    run_with_large_stack(
        "output_contract_covers_composite_facts_and_control_statements",
        || {
            let source_code = r#"
1 = 1 and 2 = 2
1 = 1 = 1

claim:
    prove:
        forall:
            1 = 1
    1 = 1

thm one_eq_one:
    prove:
        forall:
            1 = 1
    1 = 1

by thm one_eq_one()

by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "output_contract_covers_composite_facts_and_control_statements",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "output contract fixture failed:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"summary\": \"each conjunct verified in order\""),
                "and facts should keep a short composite proof summary:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"summary\": \"each chain step verified in order\""),
                "chain facts should keep a short composite proof summary:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"type\": \"chain fact\""),
                "normal output should not repeat the composite fact type inside verification:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"main_rule\": \"chain decomposition\""),
                "normal output should hide chain structural-rule debug metadata:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"role\": \"chain step\""),
                "normal output should hide chain step roles:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"step_indices\": ["),
                "normal folded output should not expose step indices:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"main_rule\": \"and decomposition\""),
                "normal output should hide and structural-rule debug metadata:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"role\": \"conjunct\""),
                "normal output should hide conjunct step roles:\n{}",
                run_output
            );
            assert_no_legacy_acceptance_field(&run_output, "successful");
            assert!(
                run_output.contains("\"type\": \"proved claim\""),
                "claim/thm statements should expose their semantic statement type:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"proof by theorem\""),
                "by thm statements should expose their semantic statement type:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"proof by cases\""),
                "by cases statements should expose their semantic statement type:\n{}",
                run_output
            );
            assert!(
                !run_output.contains("\"unknown_result\""),
                "successful output should not use failure-only unknown_result:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_cases_normal_output_lists_multiple_proved_goals_per_case() {
    run_with_large_stack(
        "by_cases_normal_output_lists_multiple_proved_goals_per_case",
        || {
            let source_code = r#"
by cases:
    prove:
        1 = 1
        2 = 2
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "by_cases_normal_output_lists_multiple_proved_goals_per_case",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "by cases multi-goal fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proof by cases\""));
            assert!(run_output.contains("\"type\": \"by cases proof\""));
            assert!(run_output.contains("\"prove_goals\": ["));
            assert!(run_output.contains("\"case_coverage\": {"));
            assert!(run_output.contains("\"cases\": ["));
            assert!(run_output.contains("\"reason\": \"case assumption\""));
            assert!(run_output.contains("\"conclusions\": ["));
            assert!(run_output.contains("\"impossible\": {"));
            assert!(run_output.contains("\"role\": \"impossible fact\""));
            assert!(run_output.contains("\"role\": \"reversed impossible fact\""));
            assert_no_legacy_acceptance_field(&run_output, "by cases");
            assert!(run_output.contains("\"1 = 1\""));
            assert!(run_output.contains("\"2 = 2\""));
        },
    );
}

#[test]
fn by_cases_detail_output_expands_case_inside_results() {
    run_with_large_stack("by_cases_detail_output_expands_case_inside_results", || {
        let source_code = r#"
by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
"#;

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("by_cases_detail_output_expands_cases");
        runtime.detail_output = true;
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) =
            render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

        assert!(
            run_succeeded,
            "by cases detail fixture failed:\n{}",
            run_output
        );
        assert!(run_output.contains("\"type\": \"proof by cases\""));
        assert_no_legacy_acceptance_field(&run_output, "detail");
        assert!(run_output.contains("\"1 = 1\""));
    });
}

#[test]
fn by_contra_output_explains_reverse_assumption_proof_and_impossible_checks() {
    run_with_large_stack(
        "by_contra_output_explains_reverse_assumption_proof_and_impossible_checks",
        || {
            let source_code = r#"
by contra 1 = 1:
    do_nothing
    impossible 1 != 1
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("by_contra_output_explains_steps");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "by contra output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"proof by contradiction\""));
            assert!(run_output.contains("\"type\": \"by contra proof\""));
            assert!(run_output.contains("\"prove_goal\": \"1 = 1\""));
            assert!(run_output.contains("\"reverse_assumption\": {"));
            assert!(run_output.contains("\"fact\": \"1 != 1\""));
            assert!(run_output.contains("\"reason\": \"by contra assumption\""));
            assert!(run_output.contains("\"proof_steps\": ["));
            assert!(run_output.contains("\"statement\": \"do_nothing\""));
            assert!(run_output.contains("\"impossible\": {"));
            assert!(run_output.contains("\"role\": \"impossible fact\""));
            assert!(run_output.contains("\"statement\": \"1 != 1\""));
            assert!(run_output.contains("\"role\": \"reversed impossible fact\""));
            assert!(run_output.contains("\"statement\": \"1 = 1\""));
            assert!(
                !run_output.contains("\"inside_results\": ["),
                "normal by contra output should keep raw inside_results folded:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_iteration_range_extension_and_theorem_outputs_explain_processes() {
    run_with_large_stack(
        "by_iteration_range_extension_and_theorem_outputs_explain_processes",
        || {
            let source_code = r#"
thm local_one_eq_one:
    prove:
        forall:
            1 = 1
    1 = 1

by thm local_one_eq_one()

by enumerate finite_set:
    prove:
        forall a {1, 2}:
            a < 3
    do_nothing

by for:
    prove:
        forall n range(0, 3):
            n < 3
    do_nothing

claim:
    prove:
        forall x range(1, 3):
            x = 1 or x = 2
    by enumerate range: x $in range(1, 3)

claim:
    prove:
        forall y closed_range(1, 2):
            y = 1 or y = 2
    by closed_range as cases: y $in 1...2

by extension {1} = {1}
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "by_iteration_range_extension_and_theorem_outputs_explain_processes",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(run_succeeded, "by output fixture failed:\n{}", run_output);
            assert!(run_output.contains("\"type\": \"by thm proof\""));
            assert!(run_output.contains("\"parameter_type_check\": {"));
            assert!(run_output.contains("\"stored_then_facts\": ["));
            assert!(run_output.contains("\"type\": \"by enumerate finite_set proof\""));
            assert!(run_output.contains("\"assignment\": {"));
            assert!(run_output.contains("\"reason\": \"enumerated assignment\""));
            assert!(run_output.contains("\"type\": \"by for proof\""));
            assert!(run_output.contains("\"iteration_mode\": \"ranges\""));
            assert!(run_output.contains("\"reason\": \"for assignment\""));
            assert!(run_output.contains("\"type\": \"by enumerate range proof\""));
            assert!(run_output.contains("\"generated_cases\":"));
            assert!(run_output.contains("\"type\": \"by closed_range as cases proof\""));
            assert!(run_output.contains("\"type\": \"by extension proof\""));
            assert!(run_output.contains("\"subset_checks\": ["));
            assert!(run_output.contains("\"reason\": \"set extensionality\""));
            assert!(
                !run_output.contains("\"inside_results\": ["),
                "normal output should keep raw by traces folded:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn by_induc_prop_bridge_and_trusted_outputs_explain_processes() {
    run_with_large_stack(
        "by_induc_prop_bridge_and_trusted_outputs_explain_processes",
        || {
            let source_code = r#"
abstract_prop local_induc_p(a)
know $local_induc_p(0)
know forall m Z:
    m >= 0
    $local_induc_p(m)
    =>:
        $local_induc_p(m + 1)
by induc n from 0:
    prove:
        $local_induc_p(n)

    prove from n = 0:
        $local_induc_p(0)

    prove induc:
        $local_induc_p(n + 1)

prop local_same_obj(x set, y set):
    x = y

by reflexive_prop:
    prove:
        forall x set:
            $local_same_obj(x, x)
    x = x

by symmetric_prop:
    prove:
        forall x, y set:
            $local_same_obj(x, y)
            =>:
                $local_same_obj(y, x)
    x = y
    y = x

have local_family set
by axiom_of_choice: set local_family:
    know forall A local_family:
        $is_nonempty_set(A)

have local_ordered_set set
abstract_prop local_leq(x, y)
by zorn_lemma: set local_ordered_set, prop local_leq:
    know $is_nonempty_set(local_ordered_set)
    know:
        forall x local_ordered_set:
            $local_leq(x, x)
        forall x, y, z local_ordered_set:
            $local_leq(x, y)
            $local_leq(y, z)
            =>:
                $local_leq(x, z)
        forall x, y local_ordered_set:
            $local_leq(x, y)
            $local_leq(y, x)
            =>:
                x = y
        forall C power_set(local_ordered_set):
            forall x, y C:
                $local_leq(x, y) or $local_leq(y, x)
            =>:
                exist u local_ordered_set st {forall! x C: {$local_leq(x, u)}}
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(
                "by_induc_prop_bridge_and_trusted_outputs_explain_processes",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "structured by output fixture failed:\n{}",
                run_output
            );
            assert!(run_output.contains("\"type\": \"by induc proof\""));
            assert!(run_output.contains("\"base_case\": {"));
            assert!(run_output.contains("\"step_case\": {"));
            assert!(run_output.contains("\"reason\": \"induction hypothesis\""));
            assert!(run_output.contains("\"type\": \"by prop registration proof\""));
            assert!(run_output.contains("\"registration\": \"reflexive\""));
            assert!(run_output.contains("\"registration\": \"symmetric\""));
            assert!(run_output.contains("\"type\": \"by axiom_of_choice proof\""));
            assert!(run_output.contains("\"label\": \"members_nonempty\""));
            assert!(run_output.contains("\"type\": \"proved in proof steps\""));
            assert!(run_output.contains("\"type\": \"by zorn_lemma proof\""));
            assert!(run_output.contains("\"label\": \"chain_upper_bound\""));
            assert!(run_output.contains("\"trusted_conclusion\":"));
            assert!(
                !run_output.contains("\"inside_results\": ["),
                "normal output should keep raw by traces folded:\n{}",
                run_output
            );
        },
    );
}

#[test]
fn unknown_fact_failure_has_structured_output_fields() {
    let source_code = "1 = 2";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("unknown_fact_failure_structured_output");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "unknown fact fixture should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"failed_goal\": \"1 = 2\""),
        "unknown fact should expose failed_goal:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"unknown_result\": {\n      \"type\": \"atomic fact unknown\""),
        "unknown atomic fact should expose fact-specific unknown_result:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"goal\": \"1 = 2\""),
        "unknown atomic fact should expose its goal:\n{}",
        run_output
    );
}

#[test]
fn detail_output_keeps_composite_fact_step_metadata() {
    let source_code = r#"
1 = 1 and 2 = 2
1 = 1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime
        .new_file_path_new_env_new_name_scope("detail_output_keeps_composite_fact_step_metadata");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "detail composite fact fixture failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"and fact\""));
    assert!(run_output.contains("\"type\": \"chain fact\""));
    assert!(run_output.contains("\"main_rule\": \"and decomposition\""));
    assert!(run_output.contains("\"main_rule\": \"chain decomposition\""));
    assert!(run_output.contains("\"role\": \"conjunct\""));
    assert!(run_output.contains("\"role\": \"chain step\""));
    assert!(run_output.contains("\"step_index\": 1"));
    assert!(run_output.contains("\"step_count\": 2"));
}

#[test]
fn and_fact_unknown_reports_failed_part() {
    let source_code = "1 = 1 and 1 = 2";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("and_fact_unknown_reports_failed_part");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "and fact fixture should fail:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"type\": \"and fact unknown\""),
        "and fact unknown should be fact-specific:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"failed_part\": {"),
        "and fact unknown should expose the failed part:\n{}",
        run_output
    );
    assert!(run_output.contains("\"stmt\": \"1 = 2\""));
    assert!(!run_output.contains("\"index\": 2"));
    assert!(!run_output.contains("\"count\": 2"));
    assert!(
        !run_output.contains("\"type\": \"atomic fact unknown\""),
        "normal output should omit redundant nested atomic unknowns:\n{}",
        run_output
    );
}

#[test]
fn chain_fact_unknown_reports_failed_chain_step() {
    let source_code = "1 = 0 = 1";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("chain_fact_unknown_reports_failed_chain_step");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "chain fact fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"chain fact unknown\""));
    assert!(
        run_output.contains("\"failed_chain_step\": {"),
        "chain fact unknown should expose the failed chain step:\n{}",
        run_output
    );
    assert!(run_output.contains("\"stmt\": \"1 = 0\""));
    assert!(!run_output.contains("\"index\": 1"));
    assert!(!run_output.contains("\"count\": 2"));
    assert!(
        !run_output.contains("\"type\": \"atomic fact unknown\""),
        "normal output should omit redundant nested atomic unknowns:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("unverified chain step"),
        "chain unknown output should not hide the failed step in a detail string:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"previous_error\": null"),
        "normal error output should omit empty previous_error fields:\n{}",
        run_output
    );
}

#[test]
fn forall_fact_unknown_reports_failed_prove() {
    let source_code = r#"
forall x R:
    x = 0
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_fact_unknown_reports_failed_prove");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "forall unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"forall unknown\""));
    assert!(run_output.contains("\"params\": ["));
    assert!(run_output.contains("\"name\": \"x\""));
    assert!(run_output.contains("\"failed_prove\": {"));
    assert!(run_output.contains("\"stmt\": \"~1x = 0\""));
    assert!(!run_output.contains("\"index\": 1"));
    assert!(!run_output.contains("\"count\": 1"));
    assert!(
        !run_output.contains("\"type\": \"atomic fact unknown\""),
        "normal output should omit redundant nested atomic unknowns:\n{}",
        run_output
    );
}

#[test]
fn forall_chain_unknown_nests_failed_chain_step() {
    let source_code = r#"
forall x R:
    x = 0 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_chain_unknown_nests_failed_chain_step");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "forall-chain unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"forall unknown\""));
    assert!(run_output.contains("\"failed_prove\": {"));
    assert!(run_output.contains("\"type\": \"chain fact unknown\""));
    assert!(run_output.contains("\"failed_chain_step\": {"));
    assert!(run_output.contains("\"stmt\": \"~1x = 0\""));
    assert!(!run_output.contains("\"index\": 1"));
    assert!(!run_output.contains("\"count\": 2"));
    assert!(!run_output.contains("unverified chain step"));
    assert!(!run_output.contains("\"previous_error\": null"));
}

#[test]
fn detail_unknown_output_keeps_failed_part_position_metadata() {
    let source_code = r#"
forall x R:
    x = 0 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "detail_unknown_output_keeps_failed_part_position_metadata",
    );
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "detail forall-chain unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"failed_prove\": {"));
    assert!(run_output.contains("\"index\": 1"));
    assert!(run_output.contains("\"count\": 1"));
    assert!(run_output.contains("\"failed_chain_step\": {"));
    assert!(run_output.contains("\"count\": 2"));
    assert!(run_output.contains("\"type\": \"atomic fact unknown\""));
}

#[test]
fn forall_iff_unknown_reports_failed_direction() {
    let source_code = r#"
forall x R:
    =>:
        x = 0
    <=>:
        x = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("forall_iff_unknown_reports_failed_direction");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "forall iff unknown fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"type\": \"forall iff unknown\""));
    assert!(run_output.contains("\"failed_direction\": \"then to iff\""));
    assert!(run_output.contains("\"type\": \"forall unknown\""));
}

#[test]
fn proof_block_failure_has_structured_then_clause_fields() {
    let source_code = r#"
claim:
    prove:
        forall:
            2 = 3
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("proof_block_failure_structured_then_clause");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded, "claim fixture should fail:\n{}", run_output);
    assert!(
        run_output.contains("\"failed_goal\": \"2 = 3\""),
        "claim failure should expose failed_goal:\n{}",
        run_output
    );
    assert!(
        !run_output.contains("\"then_clause_index\": 1"),
        "normal claim failure should hide positional metadata:\n{}",
        run_output
    );
    assert!(
        run_output.contains("\"unknown_result\": {"),
        "claim failure should expose structured unknown_result:\n{}",
        run_output
    );
}

#[test]
fn detail_proof_block_failure_keeps_then_clause_position_metadata() {
    let source_code = r#"
claim:
    prove:
        forall:
            2 = 3
    1 = 1
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "detail_proof_block_failure_keeps_then_clause_position_metadata",
    );
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "detail claim fixture should fail:\n{}",
        run_output
    );
    assert!(run_output.contains("\"then_clause_index\": 1"));
    assert!(run_output.contains("\"then_clause_count\": 1"));
}

#[test]
fn by_cases_failure_reports_case_split_failure_context() {
    run_with_large_stack(
        "by_cases_failure_reports_case_split_failure_context",
        || {
            let source_code = r#"
by cases 1 = 1:
    case 1 = 2:
        do_nothing
"#;

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("by_cases_failure_context");
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                !run_succeeded,
                "non-covering case split should fail:\n{}",
                run_output
            );
            assert!(
                run_output.contains("by cases: cannot verify that all cases cover all situations"),
                "by cases failure should keep the case split failure message:\n{}",
                run_output
            );
            assert!(
                run_output.contains("\"type\": \"proof by cases\""),
                "by cases failure should identify the failing statement:\n{}",
                run_output
            );
        },
    );
}

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
    prove:
        forall x R:
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
    prove:
        forall x R:
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
fn thm_definition_does_not_store_forall_fact_for_known_forall_use() {
    let source_code = r#"
abstract_prop target_thm_prop(x)

thm use_target_thm:
    prove:
        forall x R:
            x = 1
            =>:
                $target_thm_prop(x)

    know $target_thm_prop(x)

$target_thm_prop(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "thm_definition_does_not_store_forall_fact_for_known_forall_use",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "thm definition should not enable ordinary forall matching:\n{}",
        run_output
    );
    assert!(
        run_output.contains("Unknown"),
        "thm named-only failure should be reported as unknown:\n{}",
        run_output
    );
}

#[test]
fn lemma_definition_stores_forall_fact_for_known_forall_use() {
    let source_code = r#"
prop target_lemma_prop(x R):
    x = 1

lemma use_target_lemma:
    prove:
        forall x R:
            x = 1
            =>:
                $target_lemma_prop(x)

    x = 1

$target_lemma_prop(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "lemma_definition_stores_forall_fact_for_known_forall_use",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "lemma definition should store ordinary forall matching facts:\n{}",
        run_output
    );
    assert!(runtime
        .get_thm_definition_by_name("use_target_lemma")
        .is_some());
}

#[test]
fn lemma_definition_can_still_be_used_by_thm() {
    let source_code = r#"
prop target_lemma_prop(x R):
    x = 1

lemma use_target_lemma:
    prove:
        forall x R:
            x = 1
            =>:
                $target_lemma_prop(x)

    x = 1

by thm use_target_lemma(1)
$target_lemma_prop(1)
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("lemma_definition_can_still_be_used_by_thm");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "lemma should remain available through explicit by thm calls:\n{}",
        run_output
    );
}

#[test]
fn by_thm_releases_instantiated_then_facts() {
    let source_code = r#"
abstract_prop target_thm_prop(x)

thm use_target_thm:
    prove:
        forall x R:
            x = 1
            =>:
                $target_thm_prop(x)

    know $target_thm_prop(x)

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
}

#[test]
fn strategy_definition_auto_enables_strategy() {
    let source_code = r#"
prop target_strategy_prop(x R):
    x = 1

strategy use_target_strategy:
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

    know:
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

    let env = runtime
        .environment_stack
        .last()
        .expect("runtime should have a current environment");
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
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

    know:
        forall y R:
            y = 1
            =>:
                $target_strategy_prop(y)

stop strategy use_target_strategy

claim:
    prove:
        forall z R:
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
    prove:
        forall x R:
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

    let env = runtime
        .environment_stack
        .last()
        .expect("runtime should have a current environment");
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
fn by_strategy_is_rejected_as_removed_activation_syntax() {
    let source_code = r#"
prop target_strategy_prop(x R):
    x = 1

strategy use_target_strategy:
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

by strategy use_target_strategy
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "by_strategy_is_rejected_as_removed_activation_syntax",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        !run_succeeded,
        "`by strategy` should no longer parse as strategy activation:\n{}",
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
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

    know:
        forall y R:
            y = 1
            =>:
                $target_strategy_prop(y)

strategy use_negative_strategy:
    prove:
        forall x R:
            x != 1
            =>:
                not $target_strategy_prop(x)

    know:
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

    let env = runtime
        .environment_stack
        .last()
        .expect("runtime should have a current environment");
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
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

    know:
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
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

    know:
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

    let env = runtime
        .environment_stack
        .last()
        .expect("runtime should have a current environment");
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
    prove:
        forall x R:
            x = 1
            =>:
                $target_strategy_prop(x)

    know:
        forall y R:
            y = 1
            =>:
                $target_strategy_prop(y)

use strategy use_target_strategy
stop strategy use_target_strategy
claim:
    prove:
        $target_strategy_prop(1)
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

    let env = runtime
        .environment_stack
        .last()
        .expect("runtime should have a current environment");
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
    prove:
        forall x R:
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
    prove:
        forall x R:
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
    prove:
        forall x R:
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
    prove:
        forall x R:
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
fn run_file_from_path() {
    run_with_large_stack("run_file_from_path_large_stack", run_file_from_path_impl);
}

#[test]
fn run_file_std_module_form_is_rejected() {
    let source_code = "run_file Trig";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("run_file_std_module_form_is_rejected");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(run_output.contains("run_file expects a quoted relative or absolute file path"));
}

#[test]
fn clear_does_not_preserve_quoted_run_file_environment() {
    let run_file_path = std::env::temp_dir().join("litex-clear-quoted-run-file-test.lit");
    fs::write(
        &run_file_path,
        "abstract_prop p(x)\nknow forall x R:\n    $p(x)\n",
    )
    .unwrap();
    let run_file_path_string = run_file_path.to_string_lossy().into_owned();
    let source_code = format!("run_file \"{}\"\nclear\n$p(2)", run_file_path_string);

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "clear_does_not_preserve_quoted_run_file_environment",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    let _ = fs::remove_file(&run_file_path);

    assert!(
        !run_succeeded,
        "quoted run_file content should be cleared:\n{}",
        run_output
    );
}

#[test]
#[ignore = "std run_file was removed; import currently registers modules without executing them"]
fn std_citation_source_survives_cached_reload_after_clear() {
    let source_code = "run_file Trig\nclear\nrun_file Trig\nsin(0) = 0";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(
        "std_citation_source_survives_cached_reload_after_clear",
    );
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "cached std citation run failed:\n{}",
        run_output
    );
    assert!(run_output.contains("\"source_kind\": \"std\""));
    assert!(run_output.contains("\"source\": \"std/Trig\""));
}

fn run_file_from_path_impl() {
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
