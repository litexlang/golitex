//! Direct rejected-theorem result and transactional recovery acceptance.
use litex::execute::execute_def_thm_stmt::{
    ExecDefThmBodyFailed, ExecDefThmForallEnteredFailed, ExecDefThmForallFailed,
    ExecDefThmNonForallFailed, ExecDefThmStmtFailed, ExecDefThmStmtResult,
};
use litex::execute::{ExecDefinitionStmtResult, ExecStmtResult};
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;
fn runtime(strict: bool) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict,
            language: OutputLanguage::English,
        },
        litex::result_detail::OutputDetail::Detailed,
    )
}

#[test]
fn rejected_theorem_retains_actual_parameters_body_and_conclusion_prefix() {
    let mut rt = runtime(true);
    let source =
        include_str!("../examples/test_statements/negative/def_thm_stmt/retained-final-prefix.lit");
    let run = rt.run_litex_code(source).unwrap();
    assert!(!run.success && run.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(ExecDefThmStmtResult::Failed(
        ExecDefThmStmtFailed::Local(local),
    ))) = &run.statement_results[1]
    else {
        panic!("the original local failure is retained")
    };
    assert!(!local.goal_wd.is_failed());
    let ExecDefThmBodyFailed::Forall(ExecDefThmForallFailed::Entered {
        introduced_params,
        assumed_dom_facts,
        failure,
    }) = &local.body
    else {
        panic!("the universal proof was entered")
    };
    assert_eq!(introduced_params.defined_params.stored_fact_ids.len(), 1);
    assert_eq!(assumed_dom_facts.len(), 1);
    for id in &introduced_params.defined_params.stored_fact_ids {
        assert!(local.local_env.facts.facts_by_id.contains_key(id));
    }
    assert!(local
        .local_env
        .facts
        .facts_by_id
        .contains_key(&assumed_dom_facts[0].store_and_infer.primary_fact_id()));
    let ExecDefThmForallEnteredFailed::Conclusion {
        proof_steps,
        conclusion_proofs,
        index,
        result,
    } = failure
    else {
        panic!("the final check failed")
    };
    assert_eq!(proof_steps.len(), 2);
    assert!(proof_steps.iter().all(|step| !step.is_failed()));
    assert_eq!(*index, 1);
    assert_eq!(conclusion_proofs.len(), 1);
    assert!(!conclusion_proofs[0].is_failed() && result.is_failed());
    assert!(
        !rt.run_litex_code("by thm fail_final(0) => $P(0)\n")
            .unwrap()
            .success
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.run_litex_code("$P(1)\n").unwrap().success);
    assert!(rt.run_litex_code("have helper R = 1\n").unwrap().success);
    assert!(rt.run_litex_code("helper = 1\n").unwrap().success);
    assert!(rt.run_litex_code("thm fail_final:\n    ? forall x R:\n        x = 0\n        =>:\n            $P(x)\n    by def $P(x)\n").unwrap().success);
    assert!(
        rt.run_litex_code("by thm fail_final(0) => $P(0)\n")
            .unwrap()
            .success
    );
}

#[test]
fn rejected_nonforall_theorem_retains_only_executed_body_steps() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("thm failed_body:\n    ? 1 = 1\n    have helper R = 1\n    helper = 1\n    1 = 2\n    have later R = 3\n").unwrap();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(ExecDefThmStmtResult::Failed(
        ExecDefThmStmtFailed::Local(local),
    ))) = &run.statement_results[0]
    else {
        panic!("retained nonuniversal failure")
    };
    let ExecDefThmBodyFailed::NonForall(ExecDefThmNonForallFailed::ProofBody(failed)) = &local.body
    else {
        panic!("body failed before final goal checking")
    };
    assert_eq!(failed.step_index, 2);
    assert_eq!(failed.prior_steps.len(), 2);
    assert!(failed.prior_steps.iter().all(|step| !step.is_failed()));
    assert!(failed.result.is_failed());
    assert!(
        !rt.run_litex_code("release thm failed_body\n")
            .unwrap()
            .success
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(rt.run_litex_code("have helper R = 2\n").unwrap().success);
    assert!(rt.run_litex_code("have later R = 4\n").unwrap().success);
    assert!(rt.run_litex_code("helper = 2\n").unwrap().success);
}
