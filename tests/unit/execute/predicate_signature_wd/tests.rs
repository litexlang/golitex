use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    FailToVerifyAtomicFactWellDefinedResult, PredicateSignatureWellDefinedFailure,
};
use crate::execute::execute_fact_stmt::{FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult};
use crate::execute::execute_proof_block_stmt::{ExecClaimStmtFailed, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(strict: bool) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict, language: OutputLanguage::English,
    })
}

#[test]
fn nullary_concrete_propositions_keep_definition_wd_and_exact_arity() {
    let mut rt = runtime(true);
    assert!(rt.run_litex_code(include_str!("../../../../examples/wd/nullary_predicate_signature.lit")).unwrap().success);
    for code in ["$ready(0)\n", "not $ready(0)\n", "0 = 1\n"] {
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(!run.success, "{code}");
    }
    assert!(rt.run_litex_code("prop falsehood():\n    0 = 1\n").unwrap().success);
    assert!(!rt.run_litex_code("$falsehood()\n").unwrap().success);
    assert!(!rt.run_litex_code("prop ill_defined():\n    1 / 0 = 0\n").unwrap().success);
    assert!(!rt.run_litex_code("$ill_defined()\n").unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn nullary_abstract_propositions_preserve_strict_and_signature_checks() {
    let mut rt = runtime(false);
    assert!(rt.run_litex_code("abstract_prop opaque()\n").unwrap().success);
    assert!(!rt.run_litex_code("$opaque()\n").unwrap().success);
    assert!(rt.run_litex_code("trust $opaque()\n$opaque()\n").unwrap().success);
    for code in ["$opaque(0)\n", "not $opaque(0)\n", "by def $opaque()\n", "0 = 1\n"] {
        assert!(!rt.run_litex_code(code).unwrap().success, "{code}");
    }
    assert!(!runtime(true).run_litex_code("abstract_prop opaque()\n").unwrap().success);
}

#[test]
fn undefined_nullary_goal_still_fails_before_its_local_definition() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("claim:\n    ? $chosen()\n    prop chosen():\n        0 = 0\n    by def $chosen()\nprop chosen():\n    0 = 0\nby def $chosen()\n").unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert_eq!(run.statement_results.iter().map(|r| r.is_failed()).collect::<Vec<_>>(), [true, false, false]);
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.run_litex_code("0 = 1\n").unwrap().success);
}

#[test]
fn undefined_claim_goal_fails_before_a_later_local_declaration_can_prove_it() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("claim:\n    ? $chosen(0)\n    prop chosen(x R):\n        x = 0\n    by def $chosen(0)\nprop chosen(x R):\n    x = 1\n$chosen(0)\n0 = 1\n").unwrap();
    assert!(run.session_error.is_none());
    assert!(!run.success);
    assert!(matches!(&run.statement_results[0], ExecStmtResult::ProofBlock(
        ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Failed(ExecClaimStmtFailed::GoalWd(
            VerifyFactWellDefinedResult::Failed(FailToVerifyFactWellDefinedResult::AtomicExceptEquality(
                FailToVerifyAtomicFactWellDefinedResult::Predicate {
                    reason: PredicateSignatureWellDefinedFailure::Undefined { .. }, ..
                }
            ))
        )))
    )));
    assert_eq!(run.statement_results.iter().map(|r| r.is_failed()).collect::<Vec<_>>(),
        [true, false, true, true]);
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(rt.run_litex_code("by def $chosen(1)\n1 = 1\n").unwrap().success);
}

#[test]
fn local_helper_for_an_already_well_defined_goal_stays_valid() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("claim:\n    ? 0 = 0\n    prop chosen(x R):\n        x = 0\n    by def $chosen(0)\nprop chosen(x R):\n    x = 1\nby def $chosen(1)\n").unwrap();
    assert!(run.success, "{:?}", run.session_error);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn wrong_arity_is_rejected_in_hypotheses_of_both_polarities() {
    for definition in ["prop relation(a, b R):\n    a = b\n", "abstract_prop relation(a, b)\n"] {
        for polarity in ["", "not "] {
            let mut rt = runtime(false);
            assert!(rt.run_litex_code(definition).unwrap().success);
            let code = format!("forall x R:\n    {polarity}$relation(x)\n    =>:\n        {polarity}$relation(x)\n");
            let run = rt.run_litex_code(&code).unwrap();
            assert!(run.session_error.is_none());
            assert!(!run.success, "{code}");
            assert_eq!(rt.execution_environments_stack.len(), 1);
        }
    }
}

#[test]
fn signature_failure_is_not_an_object_failure_in_detailed_output() {
    let mut rt = runtime(true);
    assert!(rt.run_litex_code("prop relation(a, b R):\n    a = b\n").unwrap().success);
    let run = rt.run_litex_code("$relation(0)\n").unwrap();
    assert!(!run.success);
    let output = format!("{:?}", crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt));
    assert!(output.contains("predicate_signature"), "{output}");
    assert!(output.contains("arity"), "{output}");
}

#[test]
fn valid_signatures_remain_valid_in_nested_quantifiers_and_existence() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("prop relation(a, b R):\n    a = b\nforall x R:\n    $relation(x, x)\n    =>:\n        $relation(x, x)\nwitness exist u R st {$relation(u, 0)} from 0\nobtain u from exist u R st {$relation(u, 0)}\nby def $relation(u, 0)\nu = 0\n").unwrap();
    assert!(run.success, "{:?}", run.session_error);
}
