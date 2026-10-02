use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactResult};
use crate::execute::execute_fact_stmt::{ExecFactStmtResult, VerifyFactResult};
use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn ordinary_chain_cases_and_algo_keep_disjointness_and_publication_checks() {
    for keyword in ["have fn", "algo"] {
        let mut rt = runtime();
        let source = format!("{keyword} flag(x R: 0 <= x < 1 or 1 <= x < 2) N by cases:\n    case 0 <= x < 1: 0\n    case 1 <= x < 2: 1\nflag(0) = 0\nflag(1) = 1\n");
        let run = rt.run_litex_code(&source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}");
        assert_eq!(run.statement_results.len(), 3);

        for guards in [("0 <= x <= 1", "1 <= x <= 2"), ("0 <= x < 1", "1 < x < 2")] {
            let mut rt = runtime();
            let source = format!("{keyword} bad(x R: 0 <= x < 1 or 1 <= x < 2) N by cases:\n    case {}: 0\n    case {}: 1\n", guards.0, guards.1);
            let run = rt.run_litex_code(&source).unwrap();
            assert!(run.session_error.is_none(), "{source}");
            assert_eq!(run.statement_results.len(), 1);
            assert!(run.statement_results[0].is_failed(), "{source}");
            assert!(!rt
                .top_exec_env()
                .definitions
                .identifiers
                .contains_key("bad"));
            assert_eq!(rt.execution_environments_stack.len(), 1);
        }
    }
}

#[test]
fn compound_or_requires_a_checked_branch_and_preserves_its_evidence() {
    for (source, index) in [
        ("0 = 0 and 1 = 1 or 0 = 1 and 1 = 2", 0),
        ("0 = 1 and 1 = 2 or 0 = 0 and 1 = 1", 1),
        ("0 <= 0 < 1 or 1 < 0 <= 2", 0),
        ("have x R\nx = x and x <= x or x < x and x > x", 0),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}");
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) =
            run.statement_results.last().unwrap()
        else {
            panic!("fact success");
        };
        let VerifyFactResult::OrFact(r) = &s.verify_result else {
            panic!("Or result");
        };
        let VerifyOrFactResult::Success(s) = r.as_ref() else {
            panic!("Or success");
        };
        let OrFactSearchedProof::BySelectedBranch(p) = &s.searched_proof else {
            panic!("selected branch proof");
        };
        assert_eq!(p.selected_index, index);
        assert!(p.assumed_negated_branches.is_empty());
        assert!(!p.selected_branch.is_failed());
        assert_eq!(rt.execution_environments_stack.len(), 1);
        let bad = rt.run_litex_code("0 = 1").unwrap();
        assert!(
            bad.statement_results[0].is_failed(),
            "branch search leaked a false fact"
        );
    }
    let mut rt = runtime();
    let run = rt
        .run_litex_code("0 = 1 and 1 = 1 or 0 = 0 and 1 = 2")
        .unwrap();
    assert!(run.session_error.is_none());
    assert!(run.statement_results[0].is_failed());
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn induction_mismatched_headers_reject_with_the_expected_method() {
    for (method, wrong) in [("strong_induc", "induc"), ("induc", "strong_induc")] {
        let source = format!("by {method} n from 0:\n    ? n = n\n    ? from n = 0:\n        0 = 0\n    ? {wrong}:\n        n + 1 = n + 1\n");
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        assert!(!run.success);
        let error = format!("{:?}", run.session_error);
        assert!(
            error.contains(&format!("expected `? {method}:`")),
            "{error}"
        );
        let valid = source.replace(&format!("? {wrong}:"), &format!("? {method}:"));
        let run = rt.run_litex_code(&valid).unwrap();
        assert!(run.success && run.session_error.is_none(), "{valid}");
    }
}
