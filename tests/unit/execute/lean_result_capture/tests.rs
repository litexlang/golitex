use super::result::{
    ByCasesBranchClosingSuccess, ExecByCasesStmtResult, ExecByContraStmtResult, ExecByStmtResult,
};
use crate::prelude::*;

#[test]
fn witness_retains_original_binder_and_equality_stores_without_leaking_them() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("witness exist m, n R st {m = 0, n = 1} from 0, 1:\n    m = 0\n    n = 1")
        .unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "witness", None)
    );
    let ExecStmtResult::Witness(crate::execute::ExecWitnessStmtResult::WitnessExistFact(
        crate::execute::ExecWitnessExistFactStmtResult::Success(proof),
    )) = &run.statement_results[0]
    else {
        panic!("expected successful witness");
    };
    assert_eq!(proof.ambient.witness_type_checks.len(), 2);
    assert_eq!(proof.introduced_params.param_type_well_defined.len(), 1);
    assert_eq!(
        proof
            .introduced_params
            .defined_params
            .store_and_infer_results
            .len(),
        2
    );
    assert_eq!(proof.witness_equalities.len(), 2);
    assert_eq!(proof.proof_steps.len(), 2);
    for (index, parameter) in proof
        .statement
        .exist_shaped_fact_in_witness
        .plain()
        .typed_parameters
        .groups[0]
        .params
        .iter()
        .enumerate()
    {
        let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let member_id = proof
            .introduced_params
            .defined_params
            .store_and_infer_results[index]
            .primary_fact_id();
        let equality_id = proof.witness_equalities[index].primary_fact_id();
        let Fact::AtomicFact(AtomicFact::InFact(member)) =
            &proof.local_env.facts.facts_by_id[&member_id]
        else {
            panic!("binder membership");
        };
        assert_eq!(member.element.ir(), object.ir());
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) =
            &proof.local_env.facts.facts_by_id[&equality_id]
        else {
            panic!("witness equality");
        };
        assert_eq!(equality.left.ir(), object.ir());
        assert_eq!(equality.right.ir(), proof.statement.equal_tos[index].ir());
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &proof.proof_steps[index]
        else {
            panic!("expected witness body fact");
        };
        let VerifyFactResult::Equality(checked) = &step.verify_result else {
            panic!("expected witness body equality");
        };
        let VerifyEqualityResult::Success(checked) = checked.as_ref() else {
            panic!("expected verified witness body equality");
        };
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &checked.searched_proof
        else {
            panic!("expected citation of the original witness equality");
        };
        assert!(path.path.iter().any(|(_, _, id)| *id == equality_id));
        assert!(!rt.top_exec_env().facts.facts_by_id.contains_key(&member_id));
        assert!(!rt
            .top_exec_env()
            .facts
            .facts_by_id
            .contains_key(&equality_id));
        assert!(!rt
            .top_exec_env()
            .definitions
            .identifiers
            .contains_key(&parameter.name));
    }
    assert!(rt
        .top_exec_env()
        .facts
        .facts_by_id
        .contains_key(&proof.store_and_infer_result.primary_fact_id()));
}

#[test]
fn atomic_witness_retains_the_same_local_introduction_stages() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(
            "prop has_copy(a R):\n    exist m R st {m = a}\nwitness $has_copy(2) from 2",
        )
        .unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "prop witness", None)
    );
    let ExecStmtResult::Witness(crate::execute::ExecWitnessStmtResult::WitnessAtomicFact(
        crate::execute::ExecWitnessAtomicFactStmtResult::Success(proof),
    )) = &run.statement_results[1]
    else {
        panic!("expected successful prop witness");
    };
    assert_eq!(
        proof
            .introduced_params
            .defined_params
            .store_and_infer_results
            .len(),
        1
    );
    assert_eq!(proof.witness_equalities.len(), 1);
    let equality_id = proof.witness_equalities[0].primary_fact_id();
    assert_eq!(
        proof.local_env.facts.facts_by_id[&equality_id].readable_string(),
        "m = 2"
    );
    assert!(!rt
        .top_exec_env()
        .facts
        .facts_by_id
        .contains_key(&equality_id));
}

#[test]
fn witness_membership_is_checked_before_local_binder_assumptions() {
    let mut rt = runtime();
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let run = rt
        .run_litex_code("witness exist m {1} st {m = 0} from 0")
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    let ExecStmtResult::Witness(crate::execute::ExecWitnessStmtResult::WitnessExistFact(
        crate::execute::ExecWitnessExistFactStmtResult::Failed(
            crate::execute::ExecWitnessExistFactStmtFailed::WitnessType(_),
        ),
    )) = &run.statement_results[0]
    else {
        panic!("must fail at ambient witness membership");
    };
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    assert!(!rt.top_exec_env().definitions.identifiers.contains_key("m"));
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn contradiction_retains_assumption_and_return_wd_in_their_own_scopes() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("by contra:\n    ? 1 = 1\n    impossible 1 = 1")
        .unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "contra", None)
    );
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(proof))) =
        &run.statement_results[0]
    else {
        panic!("expected successful contradiction");
    };
    assert!(matches!(
        proof.reverse_assumption_wd,
        FactWellDefinedProof::AtomicExceptEquality(_)
    ));
    assert!(matches!(proof.stored_wd, FactWellDefinedProof::Equality(_)));
    assert_eq!(
        proof.negation_assumed.primary_fact_id(),
        proof.reverse_assumption_fact_id
    );
    assert!(proof
        .local_env
        .facts
        .facts_by_id
        .contains_key(&proof.reverse_assumption_fact_id));
    assert!(!rt
        .top_exec_env()
        .facts
        .facts_by_id
        .contains_key(&proof.reverse_assumption_fact_id));
    assert!(rt
        .top_exec_env()
        .facts
        .facts_by_id
        .contains_key(&proof.stored.primary_fact_id()));
}

#[test]
fn cases_keep_each_ordered_closing_store_and_return_wd() {
    let mut rt = runtime();
    let run = rt.run_litex_code("by cases:\n    ? 1 = 1\n    ? 2 = 2\n    case 0 = 0:\n        1 = 1\n    case 0 != 0:\n        impossible 0 = 0").unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "cases", None)
    );
    let ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(proof))) =
        &run.statement_results[0]
    else {
        panic!("expected successful cases");
    };
    assert_eq!(proof.stored_wd.len(), 2);
    assert_eq!(proof.stored.len(), 2);
    let branch = &proof.branches[0];
    assert!(matches!(
        branch.assumption_wd,
        FactWellDefinedProof::Equality(_)
    ));
    let ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } = &branch.closing else {
        panic!("expected ordinary conclusion closing");
    };
    assert_eq!(proved_then_facts.len(), 2);
    for (closing, expected) in proved_then_facts.iter().zip(["1 = 1", "2 = 2"]) {
        assert!(!closing.verify_result.is_failed());
        let store = &closing.store_and_infer;
        assert_eq!(
            branch.local_env.facts.facts_by_id[&store.primary_fact_id()].readable_string(),
            expected
        );
        for id in store.stored_fact_ids() {
            assert!(branch.local_env.facts.facts_by_id.contains_key(&id));
        }
    }
    for branch in &proof.branches {
        assert_eq!(
            branch.assumptions_stored.primary_fact_id(),
            branch.assumption_fact_id
        );
        assert!(branch
            .local_env
            .facts
            .facts_by_id
            .contains_key(&branch.assumption_fact_id));
        assert!(!rt
            .top_exec_env()
            .facts
            .facts_by_id
            .contains_key(&branch.assumption_fact_id));
    }
    assert!(matches!(
        proof.branches[1].closing,
        ByCasesBranchClosingSuccess::Impossible(_)
    ));
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
