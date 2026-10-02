use crate::execute::execute_by_stmt::{EnumerateAssignmentOutcome, ExecByEnumerateFiniteSetStmtResult, ExecByStmtResult};
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
    check(&mut rt, "by contra:\n    ? 1 = 1\n    impossible 1 != 1\n    by extension {1} = {1}", &[true]);
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
