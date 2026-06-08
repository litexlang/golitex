use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;
use crate::to_latex::to_latex_from_source_after_builtins;

use super::helper::run_with_large_stack;

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
fn fn_range_intro_subset_and_preimage_work() {
    let source_code = r#"
prove:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    fn_range(f) $subset R
    fn_range(f) $in power_set(R)

    have by preimage x from f(1) $in fn_range(f)
    x $in R
    x > 0
    f(1) = f(x)

prove:
    have g fn(x R, y R: x < y) R

    g(0, 1) $in fn_range(g)

    have by preimage a, b from g(0, 1) $in fn_range(g)
    a $in R
    b $in R
    a < b
    g(0, 1) = g(a, b)

prove:
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
}

#[test]
fn fn_range_on_rejects_non_unary_function() {
    let source_code = r#"
prove:
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
    let source_code = r#"
prove:
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
}

#[test]
fn have_by_preimage_checks_witness_count() {
    let source_code = r#"
prove:
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
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "have_by_exist_body_well_defined_can_use_forall_domain_fact failed:\n{}",
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
$restrict_fn_in('R(x){x}, fn(x closed_range(1, 2)) R)
$restrict_fn_in('R(x){x + 1}, fn(x closed_range(1, 2)) R)
$restrict_fn_in('(x R: x > 0) R {x}, fn(x N_pos) R)
$restrict_fn_in('R(x){x}, fn(x closed_range(1, 2)) N)
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
$restrict_fn_in('(x R: x > 0) R {x}, fn(x closed_range(-1, 1)) R)
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
fn sum_of_finite_set_core_rules() {
    let source_code = r#"
sum_of_finite_set({1, 2, 3}, 'Z(x){x}) = 1 + 2 + 3
sum_of_finite_set({}, 'Z(x){x}) = 0
sum_of_finite_set(1...3, 'Z(x){x}) = sum(1, 3, 'Z(x){x})
sum_of_finite_set({1, 2}, 'Z(x){x}) $in Z
sum_of_finite_set({1, 2}, 'N_pos(x){x}) $in N_pos

prove:
    have X finite_set
    have c Z
    sum_of_finite_set(X, '(x X) Z {c}) = count(X) * c

prove:
    have X power_set(Z)
    know $is_finite_set(X)
    sum_of_finite_set(X, '(x X) Z {x + 0}) = sum_of_finite_set(X, '(x X) Z {x})
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("sum_of_finite_set_core_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "sum_of_finite_set core rules should verify:\n{}",
        run_output
    );
}

#[test]
fn product_of_finite_set_core_rules() {
    let source_code = r#"
product_of_finite_set({2, 3, 4}, 'Z(x){x}) = 2 * 3 * 4
product_of_finite_set({}, 'Z(x){x}) = 1
product_of_finite_set(1...3, 'Z(x){x}) = product(1, 3, 'Z(x){x})
product_of_finite_set({1, 2}, 'Z(x){x}) $in Z
product_of_finite_set({1, 2}, 'N_pos(x){x}) $in N_pos
product_of_finite_set({}, 'N_pos(x){x}) $in N_pos

prove:
    have X finite_set
    have c R
    product_of_finite_set(X, '(x X) R {c}) = c ^ count(X)

prove:
    have X power_set(Z)
    know $is_finite_set(X)
    product_of_finite_set(X, '(x X) Z {x + 0}) = product_of_finite_set(X, '(x X) Z {x})
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("product_of_finite_set_core_rules");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "product_of_finite_set core rules should verify:\n{}",
        run_output
    );
}

#[test]
fn dependent_fn_param_set_uses_previous_arg() {
    let source_code = r#"
have f fn(n N_pos, x closed_range(1, n)) R
f(3, 2) = f(3, 2)
by fn as set: f
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("dependent_fn_param_set_uses_previous_arg");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "dependent_fn_param_set_uses_previous_arg failed:\n{}",
        run_output
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
prove:
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
        run_output.contains("\"type\": \"EvalStmt\"") && run_output.contains("\"0 ^ 0 = 1\""),
        "eval 0^0 should produce 1:\n{}",
        run_output
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
    assert!(run_output.contains("\"rule\": \"calculation and rational expression simplification\""));
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
"#;

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("common_power_equalities_and_order_are_builtin");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(
        run_succeeded,
        "common_power_equalities_and_order_are_builtin failed:\n{}",
        run_output
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
prove:
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
    let source_code = "1 = 1\n1 = 2";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("normal_output_omits_empty_fields");
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(!run_output.contains("\"infer_facts\": []"));
    assert!(!run_output.contains("\"inside_results\": []"));
    assert!(!run_output.contains("\"message\": \"\""));
}

#[test]
fn detail_output_keeps_empty_arrays_and_empty_strings() {
    let source_code = "1 = 1\n1 = 2";

    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope("detail_output_keeps_empty_fields");
    runtime.detail_output = true;
    let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

    assert!(!run_succeeded);
    assert!(run_output.contains("\"infer_facts\": []"));
    assert!(run_output.contains("\"inside_results\": []"));
    assert!(run_output.contains("\"message\": \"\""));
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
        run_output.contains("strict mode rejects user know statements"),
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
        run_output.contains("strict mode rejects user let statements"),
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
    assert!(output.contains("strict mode rejects user know statements"));
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
    assert!(output.contains("strict mode rejects user let statements"));
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
        run_output.contains("strict mode rejects user know statements"),
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
        run_output.contains("strict mode rejects user let statements"),
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
    assert!(run_output.contains("\"stmt\": \"run_file\""));
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
    assert!(run_output.contains("\"type\": \"cite atomic fact\""));
    assert!(run_output.contains("\"type\": \"cite prop def\""));
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
    let path: String = "./examples/01_proof_patterns/strong_induc.lit".to_string();
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
