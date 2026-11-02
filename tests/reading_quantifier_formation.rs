//! Actual failed quantified checks, scoped prefixes and formation versus truth.
use litex::ast::fact::Fact;
use litex::execute::execute_fact_stmt::verify_forall_fact::{
    FailToVerifyForallFactWellDefinedResult, ForallIntroductionFormationFailed,
    ForallIntroductionFormationFailure, ForallWellDefinedLocalFailed,
    ForallWellDefinedLocalFailure, VerifyForallFactFailed, VerifyForallFactResult,
};
use litex::execute::execute_fact_stmt::{
    ExecFactStmtResult, FailToVerifyFactWellDefinedResult, VerifyFactResult,
};
use litex::execute::{
    DefPropLocalFailed, ExecDefPropStmtFailed, ExecDefPropStmtResult, ExecDefinitionStmtResult,
    ExecStmtResult, IntroduceTypedParametersFailed,
};
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::result_detail::OutputDetail;
use litex::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        OutputDetail::Detailed,
    )
}

fn introduction(result: &ExecStmtResult) -> &ForallIntroductionFormationFailure {
    let ExecStmtResult::Fact(ExecFactStmtResult::Failed(VerifyFactResult::ForallFact(result))) =
        result
    else {
        panic!("expected failed forall statement")
    };
    let VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(
        FailToVerifyForallFactWellDefinedResult::LocalIntroduction(local),
    )) = result.as_ref()
    else {
        panic!("expected retained proof-introduction formation failure")
    };
    local
}

fn definition_formation(result: &ExecStmtResult) -> &ForallWellDefinedLocalFailure {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Failed(ExecDefPropStmtFailed::Local(local)),
    )) = result
    else {
        panic!("expected rejected predicate definition")
    };
    let DefPropLocalFailed::Condition { failed, .. } = &local.failure else {
        panic!("expected definition condition formation failure")
    };
    let FailToVerifyFactWellDefinedResult::ForallFact(
        FailToVerifyForallFactWellDefinedResult::LocalWellDefinedness(inner),
    ) = failed
    else {
        panic!("expected a retained formation-only forall scope")
    };
    inner
}

#[test]
fn failed_second_parameter_retains_only_the_actual_first_group_without_leaking_it() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("forall a R, b {1 / 0}:\n    a = a")
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    let local = introduction(&run.statement_results[0]);
    let ForallIntroductionFormationFailed::Parameters(
        IntroduceTypedParametersFailed::ParamTypeWithPrefix {
            param_type_well_defined,
            defined_params,
            ..
        },
    ) = &local.failure
    else {
        panic!("expected actual shared introduction prefix")
    };
    assert_eq!(param_type_well_defined.len(), 1);
    assert_eq!(defined_params.store_and_infer_results.len(), 1);
    for id in &defined_params.stored_fact_ids {
        assert!(local.local_env.facts.facts_by_id.contains_key(id));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| !env.facts.facts_by_id.contains_key(id)));
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.run_litex_code("a = a").unwrap().success);
    assert!(
        rt.run_litex_code("forall a R, b {1 / 2}:\n    a = a")
            .unwrap()
            .success
    );
}

#[test]
fn failed_premise_keeps_earlier_assumptions_and_enters_no_consequent_proof() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("forall x R:\n    x > 0\n    1 / (x - 1) > 0\n    =>:\n        x = x")
        .unwrap();
    let local = introduction(&run.statement_results[0]);
    let ForallIntroductionFormationFailed::Premise {
        introduced_params,
        assumed_dom_facts,
        failed_index,
        ..
    } = &local.failure
    else {
        panic!("expected stopped premise formation")
    };
    assert_eq!(introduced_params.param_type_well_defined.len(), 1);
    assert_eq!(*failed_index, 1);
    assert_eq!(assumed_dom_facts.len(), 1);
    for id in assumed_dom_facts[0].store_and_infer.stored_fact_ids() {
        assert!(local.local_env.facts.facts_by_id.contains_key(&id));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| !env.facts.facts_by_id.contains_key(&id)));
    }
    for then in &local.fact.then_facts {
        let fact: Fact = then.clone().into();
        assert!(!local
            .local_env
            .facts
            .facts_by_id
            .contains_key(&fact.fact_id()));
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn formation_only_parameter_failure_keeps_its_separate_wd_parameter_prefix() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(
            "prop quantified_parameter(t R):\n    forall a R, b {1 / 0}:\n        a = a",
        )
        .unwrap();
    let local = definition_formation(&run.statement_results[0]);
    let ForallWellDefinedLocalFailed::Parameters(prefix) = &local.failure else {
        panic!("expected WD-only parameter introduction")
    };
    assert_eq!(prefix.param_type_well_defined.len(), 1);
    assert_eq!(prefix.defined_params.store_and_infer_results.len(), 1);
    for id in &prefix.defined_params.stored_fact_ids {
        assert!(local.local_env.facts.facts_by_id.contains_key(id));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| !env.facts.facts_by_id.contains_key(id)));
    }
    assert!(rt
        .execution_environments_stack
        .iter()
        .all(|env| env.lookup_def_prop("quantified_parameter").is_none()));
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn checked_false_consequent_is_only_well_formed_and_is_never_assumed_or_proved() {
    let mut rt = runtime();
    let run = rt.run_litex_code("prop check_only(t R):\n    forall x R:\n        x > 0\n        =>:\n            x = 0\n            1 / (x - 1) > 0\n            x = x").unwrap();
    let local = definition_formation(&run.statement_results[0]);
    let ForallWellDefinedLocalFailed::Conclusion {
        assumed_dom_facts,
        checked_then,
        failed_index,
        ..
    } = &local.failure
    else {
        panic!("expected formation-only consequent prefix")
    };
    assert_eq!(assumed_dom_facts.len(), 1);
    assert_eq!(checked_then.len(), 1);
    assert_eq!(*failed_index, 1);
    for then in &local.fact.then_facts {
        let fact: Fact = then.clone().into();
        assert!(!local
            .local_env
            .facts
            .facts_by_id
            .contains_key(&fact.fact_id()));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| !env.facts.facts_by_id.contains_key(&fact.fact_id())));
    }
    assert!(rt
        .execution_environments_stack
        .iter()
        .all(|env| env.lookup_def_prop("check_only").is_none()));
    assert!(rt.run_litex_code("prop check_only(t R):\n    forall x R:\n        x > 0\n        x != 1\n        =>:\n            x = 0\n            1 / (x - 1) > 0\n            x = x").unwrap().success);
    let instance = rt.run_litex_code("by def $check_only(2)").unwrap();
    assert!(!instance.success && instance.session_error.is_none());
    assert_eq!(rt.execution_environments_stack.len(), 1);
}
