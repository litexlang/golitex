use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn check(code: &str, needles: &[&str]) {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime(language);
        let before = rt
            .execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect::<Vec<_>>();
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none());
        let after = rt
            .execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            before, after,
            "failure projection must not publish local facts"
        );
        for json in [
            crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt),
            crate::json_output::project_stmt_normal(&run.statement_results[0], &rt),
        ] {
            let text = json.stringify();
            for needle in needles {
                assert!(text.contains(needle), "{needle}: {text}");
            }
        }
    }
}

#[test]
fn false_claim_conclusion_retains_the_exact_goal() {
    check("claim:\n    ? 1 = 2\n", &["conclusion", "1 = 2"]);
}

#[test]
fn extension_retains_nested_failed_claim() {
    check("by extension:\n    ? {1} = {2}\n    claim:\n        ? forall x {1}:\n            x $in {2}\n", &["proof_body", "conclusion", "x $in {2}"]);
}

#[test]
fn cases_retains_branch_and_nested_failed_body_step() {
    check("by cases:\n    ? 1 = 1\n    case 0 = 0:\n        claim:\n            ? 1 = 1\n            0 = 1\n    case 0 != 0:\n        1 = 1\n", &["branch", "proof_body", "0 = 1"]);
}

#[test]
fn contradiction_retains_failed_body_before_closing() {
    check(
        "by contra:\n    ? 0 = 1\n    0 = 1\n    impossible 0 = 0\n",
        &["proof_body", "0 = 1"],
    );
}

#[test]
fn ill_defined_claim_retains_wd_before_body() {
    check("claim:\n    ? 1 / 0 = 1 / 0\n", &["goal_wd", "1 / 0"]);
}
