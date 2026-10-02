use crate::execute::execute_by_stmt::{EnumerateAssignmentOutcome, ExecByEnumerateFiniteSetStmtResult, ExecByForStmtResult, ExecByStmtResult};
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(strict: bool) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict, language: OutputLanguage::English,
    })
}

fn check(rt: &mut Runtime, code: &str, expected: &[bool]) {
    let result = rt.run_litex_code(code).expect("run input");
    assert!(result.session_error.is_none(), "{code}\n{:?}", result.session_error);
    assert_eq!(result.statement_results.iter().map(|s| !s.is_failed()).collect::<Vec<_>>(), expected, "{code}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn strict_rejects_template_trust_at_top_level_and_in_proof_bodies() {
    let source = "template<S set>:\n    trust have hidden R:\n        hidden = 1\n";
    for code in [source.to_string(), format!("by extension:\n    ? {{1}} = {{1}}\n{}", source.lines().map(|line| format!("    {line}\n")).collect::<String>())] {
        let mut rt = runtime(true);
        let run = rt.run_litex_code(&code).unwrap();
        assert!(!run.success);
        let error = format!("{:?}", run.session_error);
        assert!(error.contains("forbidden") && error.contains("-strict"), "{error}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        check(&mut rt, "have hidden R = 2", &[true]);
    }
    check(&mut runtime(false), source, &[true]);
    check(&mut runtime(true), "template<S set>:\n    have carrier set = S", &[true]);
}

#[test]
fn finite_guards_skip_only_proved_false_premises_and_reject_false_conclusions() {
    for method in ["enumerate finite_set", "for"] {
        let prefix = format!("by {method}:\n    ? forall n {{0, 1, 2}}:\n        n > 0\n        =>:\n");
        check(&mut runtime(true), &(prefix.clone() + "            n != 0"), &[true]);
        check(&mut runtime(true), &(prefix + "            n = 0"), &[false]);
        check(&mut runtime(true), &format!("by {method}:\n    ? forall n {{}}:\n        n = n"), &[true]);
        check(&mut runtime(true), &format!("have a R\nby {method}:\n    ? forall n {{0}}:\n        a = 0\n        =>:\n            0 = 1"), &[true, false]);
        check(&mut runtime(true), &format!("have a R\nby {method}:\n    ? forall n {{0}}:\n        a = 0\n        =>:\n            a = 0"), &[true, true]);
        check(&mut runtime(true), &format!("by {method}:\n    ? forall p cart({{0, 1}}, {{2, 3}}):\n        p = p"), &[false]);
    }
}

#[test]
fn finite_numeric_carriers_verify_symbolic_arithmetic_and_each_assignment() {
    for method in ["enumerate finite_set", "for"] {
        let mut rt = runtime(true);
        let run = rt.run_litex_code(&format!("by {method}:\n    ? forall n {{0, 1}}:\n        n + 0 = n")).unwrap();
        assert!(run.success, "{}", crate::json_output::project_stmt_normal(&run.statement_results[0], &rt).stringify());
        let assignments = match &run.statement_results[0] {
            ExecStmtResult::By(ExecByStmtResult::EnumerateFiniteSet(ExecByEnumerateFiniteSetStmtResult::Success(success))) => &success.assignments,
            ExecStmtResult::By(ExecByStmtResult::For(ExecByForStmtResult::Success(success))) => &success.assignments,
            _ => panic!("finite enumeration success"),
        };
        assert_eq!(assignments.len(), 2);
        for assignment in assignments {
            let EnumerateAssignmentOutcome::Proved { then_proofs, .. } = &assignment.outcome else { panic!("each assignment must be proved"); };
            assert_eq!(then_proofs.len(), 1);
        }
        let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
        for field in ["FiniteSetSubsetMembership", "source_membership_proof", "member_in_proofs", "binding_assumptions", "then_proofs"] {
            assert!(detailed.contains(field), "missing {field}: {detailed}");
        }
        check(&mut rt, "have n R = 5", &[true]);
        check(&mut runtime(true), &format!("by {method}:\n    ? forall n {{0, 1}}:\n        n + 0 = 0"), &[false]);
        check(&mut runtime(true), &format!("by {method}:\n    ? forall n {{0, {{1}}}}:\n        n + 0 = n"), &[false]);
        check(&mut runtime(true), &format!("by {method}:\n    ? forall n {{{{1}}}}:\n        n + 0 = n"), &[false]);
        check(&mut runtime(true), &format!("by {method}:\n    ? forall n {{0, 1}}:\n        n / 0 = n"), &[false]);
    }
    // No concrete equality for n is needed to establish the carrier or identity.
    check(&mut runtime(true), "forall n {0, 1}:\n    n + 0 = n", &[true]);
    check(&mut runtime(true), "have n {0, 1}\nn $in N\nn + 0 = n", &[true, true, true]);
    check(&mut runtime(true), "have a R\nhave n {a}\nn $in R", &[true, true, true]);
    check(&mut runtime(true), "have a R*\nhave n {a, 0}\nn $in R", &[true, true, true]);
    // A set-valued member never acquires a numeric type. One positive member
    // is insufficient to lift a two-member carrier to N+.
    check(&mut runtime(true), "have n {{1}}\nn $in C", &[true, false]);
    check(&mut runtime(true), "have n {0, 1}\nn $in N+", &[true, false]);
    check(&mut runtime(true), "have n R\nn $in {n}\nn $in N", &[true, true, false]);
}

#[test]
fn trust_have_display_replays_body_names_and_preserves_strict_policy() {
    for source in [
        "trust have trusted_a R:\n    trusted_a = 1",
        "trust have trusted_a, trusted_b R:\n    trusted_a = 1\n    trusted_b = 2",
        "trust have trusted_a R",
    ] {
        let mut rt = runtime(false);
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success, "{source}");
        let normal = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        let rendered = normal.as_object().unwrap().get("statement").unwrap().as_str().unwrap();
        assert!(rendered.starts_with("trust have "), "{rendered}");
        check(&mut runtime(false), rendered, &[true]);
        let strict = runtime(true).run_litex_code(rendered).unwrap();
        assert!(!strict.success);
        assert!(format!("{:?}", strict.session_error).contains("forbidden"));
    }
}

#[test]
fn finite_proof_bodies_keep_binders_premises_and_nested_proof_evidence() {
    let mut rt = runtime(true);
    check(&mut rt, "prop positive(x R):\n    x > 0", &[true]);
    let run = rt.run_litex_code("by enumerate finite_set:\n    ? forall n {0, 1, 2}:\n        n > 0\n        =>:\n            n != 0\n    by def $positive(n)").unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let ExecStmtResult::By(ExecByStmtResult::EnumerateFiniteSet(ExecByEnumerateFiniteSetStmtResult::Success(success))) = &run.statement_results[0] else { panic!("enumeration success"); };
    assert_eq!(success.assignments.len(), 3);
    assert!(matches!(success.assignments[0].outcome, EnumerateAssignmentOutcome::Skipped { .. }));
    for assignment in &success.assignments[1..] {
        let EnumerateAssignmentOutcome::Proved { proof_steps, .. } = &assignment.outcome else { panic!("proved assignment"); };
        assert!(matches!(proof_steps[0], ExecStmtResult::By(ExecByStmtResult::Def(_))));
    }
    check(&mut rt, "have n R = 5", &[true]);
}

#[test]
fn nested_by_steps_preserve_helper_scope_and_failure_rollback() {
    let mut rt = runtime(true);
    check(&mut rt, "by extension:\n    ? {1} = {1}\n    have helper N = 1\n    by def {1} $subset {1}\nhave helper N = 2", &[true, true]);
    check(&mut rt, "by extension:\n    ? {1} = {1}\n    have discarded N = 1\n    0 = 1\nhave discarded N = 2", &[false, true]);
    check(&mut rt, "by cases:\n    ? 1 = 1\n    case 1 = 1:\n        by extension {1} = {1}", &[true]);
    check(&mut rt, "by contra:\n    ? 1 = 1\n    by extension {1} = {1}\n    impossible 1 != 1", &[true]);
    check(&mut rt, "have fn f(x R) R = x\nhave fn g(x R) R = x\nby fn_extension:\n    ? f = g\n    by extension {1} = {1}", &[true, true, true]);
}

#[test]
fn eval_checks_source_domain_before_rewrite_or_execution() {
    let mut rt = runtime(true);
    check(&mut rt, "algo identity(x N) N by cases:\n    case x = x: x", &[true]);
    for expression in ["identity(-1)", "identity(-1) + 1", "1 / 0", "sqrt(-1)"] {
        let run = rt.run_litex_code(&format!("eval {expression}")).unwrap();
        assert!(run.session_error.is_none());
        assert!(matches!(&run.statement_results[0], ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(ExecEvalStmtFailed::WellDefined(_))))), "{expression}");
    }
    check(&mut rt, "eval identity(0)\neval identity(2) + 1\neval 1 / 2", &[true, true, true]);
    check(&mut rt, "0 = 1", &[false]);
}

#[test]
fn statement_boundary_json_retains_nested_proofs_and_wd_failure() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("by enumerate finite_set:\n    ? forall n {0, 1}:\n        n > 0\n        =>:\n            n != 0\n    by extension {1} = {1}").unwrap();
    assert!(run.success);
    let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    for field in ["assignments", "binding_assumptions", "skipped_false_premise", "negated_premise", "proof_steps", "by_extension", "then_proofs", "store_and_infer"] {
        assert!(detailed.contains(field), "missing {field}: {detailed}");
    }
    check(&mut rt, "algo identity(x N) N by cases:\n    case x = x: x", &[true]);
    let run = rt.run_litex_code("eval identity(-1)").unwrap();
    let normal = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt).stringify();
    assert!(normal.contains("well_defined") && normal.contains("identity(-1)"), "{normal}");
    let run = rt.run_litex_code("eval identity(1)").unwrap();
    let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(detailed.contains("source_well_defined"), "{detailed}");
}

#[test]
fn run_examples_statement_boundary_tracers() {
    for (strict, code) in [
        (true, include_str!("../../../../examples/stmt_nodes/by/finite_set_conditional_proof_steps.lit")),
        (true, include_str!("../../../../examples/stmt_nodes/command/eval_source_domain.lit")),
        (false, include_str!("../../../../examples/stmt_nodes/unsafe/template_strict_policy.lit")),
    ] {
        let run = runtime(strict).run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}\n{:?}", run.session_error);
    }
}
