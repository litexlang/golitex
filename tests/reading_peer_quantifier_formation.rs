//! Actual peer-WD prefixes and scope retention, without proving quantified truth.
use litex::ast::fact::{AtomicFact, Fact};
use litex::ast::obj::{IdentifierObj, Literal, Obj};
use litex::exec_env::exec_env::ExecEnv;
use litex::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedWellDefinedLocalFailed, FailToVerifyExistShapedFactWellDefinedResult,
};
use litex::execute::execute_fact_stmt::verify_forall_fact_with_iff::{
    FailToVerifyForallFactWithIffWellDefinedResult, ForallIffWellDefinedLocalFailed,
};
use litex::execute::execute_fact_stmt::verify_not_forall_fact::{
    FailToVerifyNotForallFactWellDefinedResult, NotForallWellDefinedLocalFailed,
};
use litex::execute::execute_fact_stmt::well_defined_results::VerifyAndDefineWdParametersFailed;
use litex::execute::execute_fact_stmt::FailToVerifyFactWellDefinedResult;
use litex::execute::{
    DefPropLocalFailed, ExecDefPropStmtFailed, ExecDefPropStmtResult, ExecDefinitionStmtResult,
    ExecStmtResult,
};
use litex::instantiate::quantifier_free_fact_to_fact;
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::result_detail::OutputDetail;
use litex::runtime::{FactId, Runtime};

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

fn condition_failure(result: &ExecStmtResult) -> &FailToVerifyFactWellDefinedResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Failed(ExecDefPropStmtFailed::Local(local)),
    )) = result
    else {
        panic!("expected a failed predicate definition")
    };
    let DefPropLocalFailed::Condition { failed, .. } = &local.failure else {
        panic!("expected a stopped definition condition")
    };
    failed
}

fn parameter_prefix(
    failed: &FailToVerifyFactWellDefinedResult,
) -> (&VerifyAndDefineWdParametersFailed, &ExecEnv) {
    match failed {
        FailToVerifyFactWellDefinedResult::ExistFact(
            FailToVerifyExistShapedFactWellDefinedResult::Local(local),
        ) => match &local.failure {
            ExistShapedWellDefinedLocalFailed::Parameters(prefix) => (prefix, &local.local_env),
            _ => panic!("expected stopped existential parameter formation"),
        },
        FailToVerifyFactWellDefinedResult::NotForall(
            FailToVerifyNotForallFactWellDefinedResult::Local(local),
        ) => match &local.failure {
            NotForallWellDefinedLocalFailed::Parameters(prefix) => (prefix, &local.local_env),
            _ => panic!("expected stopped not-forall parameter formation"),
        },
        FailToVerifyFactWellDefinedResult::ForallFactWithIff(
            FailToVerifyForallFactWithIffWellDefinedResult::Local(local),
        ) => match &local.failure {
            ForallIffWellDefinedLocalFailed::Parameters(prefix) => (prefix, &local.local_env),
            _ => panic!("expected stopped equivalence parameter formation"),
        },
        _ => panic!("expected a retained peer formation failure"),
    }
}

fn local_only(rt: &Runtime, env: &ExecEnv, ids: &[FactId]) {
    for id in ids {
        assert!(env.facts.facts_by_id.contains_key(id));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|outer| !outer.facts.facts_by_id.contains_key(id)));
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn five_surfaces_keep_the_actual_first_parameter_group_and_rollback_on_failure() {
    for body in [
        "exist a R, b {1 / 0} st {a = a}",
        "exist! a R, b {1 / 0} st {a = a}",
        "not exist a R, b {1 / 0} st {a = a}",
        "not forall a R, b {1 / 0}:\n        a = a",
        "forall a R, b {1 / 0}:\n        =>:\n            a = a\n        <=>:\n            a = a",
    ] {
        let mut rt = runtime();
        let source = format!("prop candidate(t R):\n    {body}");
        let run = rt.run_litex_code(&source).unwrap();
        assert!(!run.success && run.session_error.is_none());
        let (prefix, env) = parameter_prefix(condition_failure(&run.statement_results[0]));
        assert_eq!(prefix.param_type_well_defined.len(), 1);
        assert_eq!(prefix.defined_params.store_and_infer_results.len(), 1);
        local_only(&rt, env, &prefix.defined_params.stored_fact_ids);
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| env.lookup_def_prop("candidate").is_none()));
        assert!(
            rt.run_litex_code(&source.replace("{1 / 0}", "{1 / 2}"))
                .unwrap()
                .success
        );
    }
}

#[test]
fn first_parameter_failure_keeps_an_empty_prefix_instead_of_inventing_bindings() {
    for body in [
        "exist a {1 / 0} st {a = a}",
        "not forall a {1 / 0}:\n        a = a",
        "forall a {1 / 0}:\n        =>:\n            a = a\n        <=>:\n            a = a",
    ] {
        let mut rt = runtime();
        let run = rt
            .run_litex_code(&format!("prop empty_prefix(t R):\n    {body}"))
            .unwrap();
        let (prefix, _) = parameter_prefix(condition_failure(&run.statement_results[0]));
        assert!(prefix.param_type_well_defined.is_empty());
        assert!(prefix.defined_params.store_and_infer_results.is_empty());
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn existential_body_prefix_is_only_a_local_candidate_condition_not_a_witness() {
    for shape in ["exist", "exist!", "not exist"] {
        let mut rt = runtime();
        let source = format!(
            "prop candidate_body(t R):\n    {shape} x R st {{x > 0, 1 / (x - 1) > 0, x = x}}"
        );
        let run = rt.run_litex_code(&source).unwrap();
        let FailToVerifyFactWellDefinedResult::ExistFact(
            FailToVerifyExistShapedFactWellDefinedResult::Local(local),
        ) = condition_failure(&run.statement_results[0])
        else {
            panic!("expected existential body WD failure")
        };
        let ExistShapedWellDefinedLocalFailed::Body {
            assumed_body_facts,
            failed_index,
            ..
        } = &local.failure
        else {
            panic!("expected stopped candidate body")
        };
        assert_eq!(*failed_index, 1);
        assert_eq!(assumed_body_facts.len(), 1);
        local_only(
            &rt,
            &local.local_env,
            &assumed_body_facts[0].store_and_infer.stored_fact_ids(),
        );
        for clause in &local.fact.plain().facts[1..] {
            assert!(!local
                .local_env
                .facts
                .facts_by_id
                .contains_key(&quantifier_free_fact_to_fact(clause.clone()).fact_id()));
        }
        assert!(!local
            .local_env
            .facts
            .facts_by_id
            .contains_key(&local.fact.plain().fact_id));
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| env.lookup_def_prop("candidate_body").is_none()));
    }
}

#[test]
fn not_forall_false_consequent_is_formation_only_and_no_counterexample_is_stored() {
    let mut rt = runtime();
    let run = rt.run_litex_code("prop refuted(t R):\n    not forall x R:\n        x > 0\n        =>:\n            x = 0\n            1 / (x - 1) > 0\n            x = x").unwrap();
    let FailToVerifyFactWellDefinedResult::NotForall(
        FailToVerifyNotForallFactWellDefinedResult::Local(local),
    ) = condition_failure(&run.statement_results[0])
    else {
        panic!("expected not-forall formation failure")
    };
    let NotForallWellDefinedLocalFailed::Conclusion {
        assumed_dom_facts,
        checked_then,
        failed_index,
        ..
    } = &local.failure
    else {
        panic!("expected consequent formation prefix")
    };
    assert_eq!(assumed_dom_facts.len(), 1);
    assert_eq!(checked_then.len(), 1);
    assert_eq!(*failed_index, 1);
    local_only(
        &rt,
        &local.local_env,
        &assumed_dom_facts[0].store_and_infer.stored_fact_ids(),
    );
    for clause in &local.fact.then_facts {
        assert!(!local
            .local_env
            .facts
            .facts_by_id
            .contains_key(&quantifier_free_fact_to_fact(clause.clone()).fact_id()));
    }
    assert!(!local
        .local_env
        .facts
        .facts_by_id
        .contains_key(&local.fact.fact_id));
}

#[test]
fn equivalence_sides_are_not_assumed_or_proved_during_formation() {
    for right in [false, true] {
        let mut rt = runtime();
        let left = if right {
            "x = 0"
        } else {
            "x = 0\n            1 / (x - 1) > 0\n            x = x"
        };
        let rhs = if right {
            "x = x\n            1 / (x - 1) > 0\n            x = x"
        } else {
            "x = x"
        };
        let run = rt.run_litex_code(&format!("prop equivalent(t R):\n    forall x R:\n        x > 0\n        =>:\n            {left}\n        <=>:\n            {rhs}")).unwrap();
        let FailToVerifyFactWellDefinedResult::ForallFactWithIff(
            FailToVerifyForallFactWithIffWellDefinedResult::Local(local),
        ) = condition_failure(&run.statement_results[0])
        else {
            panic!("expected equivalence WD failure")
        };
        match &local.failure {
            ForallIffWellDefinedLocalFailed::LeftSide {
                checked_then,
                failed_index,
                ..
            } => {
                assert!(!right);
                assert_eq!(checked_then.len(), 1);
                assert_eq!(*failed_index, 1);
            }
            ForallIffWellDefinedLocalFailed::RightSide {
                checked_then,
                checked_iff,
                failed_index,
                ..
            } => {
                assert!(right);
                assert_eq!(checked_then.len(), 1);
                assert_eq!(checked_iff.len(), 1);
                assert_eq!(*failed_index, 1);
            }
            _ => panic!("expected an actual side formation prefix"),
        }
        for clause in local
            .fact
            .forall_fact
            .then_facts
            .iter()
            .chain(local.fact.iff_facts.iter())
        {
            let fact: Fact = clause.clone().into();
            assert!(!local
                .local_env
                .facts
                .facts_by_id
                .contains_key(&fact.fact_id()));
        }
        assert!(!local
            .local_env
            .facts
            .facts_by_id
            .contains_key(&local.fact.fact_id));
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn actual_inferences_from_a_candidate_condition_remain_in_its_retained_scope() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("prop nonzero_value(x R):\n    x != 0")
            .unwrap()
            .success
    );
    let run = rt
        .run_litex_code(
            "prop candidate(t R):\n    exist x R st {$nonzero_value(x), 1 / (x - 1) > 0, x = x}",
        )
        .unwrap();
    let FailToVerifyFactWellDefinedResult::ExistFact(
        FailToVerifyExistShapedFactWellDefinedResult::Local(local),
    ) = condition_failure(&run.statement_results[0])
    else {
        panic!("expected retained candidate scope")
    };
    let (id, _) = local
        .local_env
        .facts
        .facts_by_id
        .iter()
        .find(|(_, fact)| {
            matches!(fact,
                Fact::AtomicFact(AtomicFact::NotEqualFact(neq))
                    if matches!(&neq.left, Obj::Identifier(IdentifierObj::Plain { id, .. })
                        if *id == local.fact.plain().typed_parameters.groups[0].params[0].id)
                    && matches!(&neq.right, Obj::Literal(Literal::Number(number))
                        if number.normalized_value == "0")
            )
        })
        .expect("the actual predicate expansion is retained");
    local_only(&rt, &local.local_env, &[*id]);
    assert!(rt
        .execution_environments_stack
        .iter()
        .all(|env| env.lookup_def_prop("candidate").is_none()));
}
