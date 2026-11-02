//! Explicit assumptions: formation is checked before any body clause is stored.
use litex::execute::execute_def_template_stmt::{
    DefTemplateLocalFailed, ExecDefTemplateStmtFailed, ExecDefTemplateStmtResult,
};
use litex::execute::execute_unsafe_stmt::{
    ExecTrustHaveFailure, ExecTrustHaveStmtFailed, ExecTrustHaveStmtResult,
    TrustHaveFormationFailed,
};
use litex::execute::{
    ExecDefinitionStmtResult, ExecStmtResult, ExecTrustBoundaryStmtResult,
    IntroduceTypedParametersFailed,
};
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::result_detail::OutputDetail;
use litex::runtime::Runtime;

fn runtime(strict: bool) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict,
            language: OutputLanguage::English,
        },
        OutputDetail::Detailed,
    )
}
fn context(result: &ExecStmtResult) -> &ExecTrustHaveFailure {
    let ExecStmtResult::Trust(ExecTrustBoundaryStmtResult::TrustHaveStmt(
        ExecTrustHaveStmtResult::Failed(ExecTrustHaveStmtFailed::Retained(context)),
    )) = result
    else {
        panic!("expected retained trust-have failure")
    };
    context
}

#[test]
fn completed_parameter_group_is_retained_but_not_committed_after_failure() {
    let mut rt = runtime(false);
    let run = rt
        .run_litex_code("trust have a R, b {1 / 0}:\n    a = a")
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    let ctx = context(&run.statement_results[0]);
    let TrustHaveFormationFailed::Parameters(IntroduceTypedParametersFailed::ParamTypeWithPrefix {
        param_type_well_defined,
        defined_params,
        ..
    }) = &ctx.failure
    else {
        panic!("expected partial parameter introduction")
    };
    assert_eq!(param_type_well_defined.len(), 1);
    assert_eq!(defined_params.store_and_infer_results.len(), 1);
    let env = ctx.local_env.as_ref().unwrap();
    for id in &defined_params.stored_fact_ids {
        assert!(env.facts.facts_by_id.contains_key(id));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| !env.facts.facts_by_id.contains_key(id)));
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(
        rt.run_litex_code("trust have a R, b {1 / 2}:\n    a = a")
            .unwrap()
            .success
    );
}

#[test]
fn body_prefix_is_formed_but_not_assumed_before_all_body_checks_finish() {
    let mut rt = runtime(false);
    let run = rt
        .run_litex_code("trust have a R:\n    a != 0\n    1 / a $in R\n    a = a")
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    let ctx = context(&run.statement_results[0]);
    let TrustHaveFormationFailed::BodyFact {
        introduced_params,
        rewritten_body,
        checked_body,
        failed_index,
        ..
    } = &ctx.failure
    else {
        panic!("expected stopped body formation")
    };
    assert_eq!(introduced_params.param_type_well_defined.len(), 1);
    assert_eq!(*failed_index, 1);
    assert_eq!(checked_body.len(), 1);
    assert_eq!(rewritten_body.len(), 3);
    let env = ctx.local_env.as_ref().unwrap();
    for fact in rewritten_body {
        assert!(!env.facts.facts_by_id.contains_key(&fact.fact_id()));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| !env.facts.facts_by_id.contains_key(&fact.fact_id())));
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(
        rt.run_litex_code("trust have a R:\n    a != 0")
            .unwrap()
            .success
    );
    assert!(rt.run_litex_code("1 / a $in R").unwrap().success);
}

#[test]
fn empty_parameter_prefix_is_retained_without_inventing_a_definition() {
    let mut rt = runtime(false);
    let run = rt
        .run_litex_code("trust have a {1 / 0}:\n    a = a")
        .unwrap();
    assert!(!run.success);
    let ctx = context(&run.statement_results[0]);
    let TrustHaveFormationFailed::Parameters(IntroduceTypedParametersFailed::ParamTypeWithPrefix {
        param_type_well_defined,
        defined_params,
        ..
    }) = &ctx.failure
    else {
        panic!("expected first parameter WD failure")
    };
    assert!(param_type_well_defined.is_empty());
    assert!(defined_params.store_and_infer_results.is_empty());
    assert!(ctx.local_env.as_ref().unwrap().facts.facts_by_id.is_empty());
}

#[test]
fn template_body_shares_the_actual_template_environment_without_an_extra_scope() {
    let mut rt = runtime(false);
    let run = rt
        .run_litex_code(
            "template<A set>:\n    trust have a R:\n        a != 0\n        1 / a $in R",
        )
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Failed(ExecDefTemplateStmtFailed::Local(local)),
    )) = &run.statement_results[0]
    else {
        panic!("expected template local failure")
    };
    let DefTemplateLocalFailed::Body {
        failed: ExecDefTemplateStmtFailed::BodyTrustHave(ExecTrustHaveStmtFailed::Retained(ctx)),
        ..
    } = &local.failure
    else {
        panic!("expected failed direct trust-have body")
    };
    assert!(ctx.local_env.is_none());
    let TrustHaveFormationFailed::BodyFact {
        introduced_params,
        rewritten_body,
        ..
    } = &ctx.failure
    else {
        panic!("expected body WD failure")
    };
    for id in &introduced_params.defined_params.stored_fact_ids {
        assert!(local.local_env.facts.facts_by_id.contains_key(id));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| !env.facts.facts_by_id.contains_key(id)));
    }
    for fact in rewritten_body {
        assert!(!local
            .local_env
            .facts
            .facts_by_id
            .contains_key(&fact.fact_id()));
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(
        rt.run_litex_code("template<A set>:\n    trust have a R:\n        a != 0")
            .unwrap()
            .success
    );
}

#[test]
fn strict_policy_stops_before_trust_have_entry_and_tentative_state() {
    for source in [
        "trust have a R:\n    a != 0",
        "template<A set>:\n    trust have a R:\n        a != 0",
    ] {
        let mut rt = runtime(true);
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(run.statement_results.is_empty());
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(rt.execution_environments_stack[0]
            .facts
            .facts_by_id
            .is_empty());
    }
}

#[test]
fn successful_false_body_remains_an_explicit_assumption_not_a_truth_check() {
    let mut rt = runtime(false);
    let run = rt
        .run_litex_code("trust have a R:\n    a = 0\n    a = 1")
        .unwrap();
    assert!(run.success);
    let ExecStmtResult::Trust(ExecTrustBoundaryStmtResult::TrustHaveStmt(
        ExecTrustHaveStmtResult::Success(ok),
    )) = &run.statement_results[0]
    else {
        panic!("expected successful explicit assumptions")
    };
    assert_eq!(ok.body_facts_well_defined.len(), 2);
    assert_eq!(ok.body_store_and_infer_results.len(), 2);
}
