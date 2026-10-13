use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::*;
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactResult;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferResult};

fn execute(source: &str) -> RunLitexCodeResult {
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    Runtime::new(command).run_litex_code(source).unwrap()
}

#[test]
fn ordered_builder_formation_retains_binder_and_original_guard_store() {
    let result = execute("have A set = {x R: x != 0, 1 / x > 0}\n");
    assert!(result.success);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
    )) = &result.statement_results[0]
    else {
        panic!("set definition")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(wd)),
        ..
    }) = &p.equal_to_well_defined[0]
    else {
        panic!("builder formation")
    };
    assert_eq!(wd.defined_params.store_and_infer_results.len(), 1);
    assert_eq!(wd.assumed_facts.len(), 2);
    let guard_id = wd.assumed_facts[0].store_and_infer.primary_fact_id();
    let FactWellDefinedProof::AtomicExceptEquality(order) = &wd.assumed_facts[1].well_defined
    else {
        panic!("order WD")
    };
    let division = order
        .well_defined_of_each_parameter
        .iter()
        .find_map(|p| match p {
            ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ArithmeticOperator(
                        ArithmeticOperatorObjWellDefinedProofByDef::Div(wd),
                    ),
                ..
            } => Some(wd),
            _ => None,
        })
        .expect("actual division WD, not predicate truth");
    assert!(division.requirement_fact_verified.iter().any(|p| match p {
        VerifyFactResult::AtomicExceptEquality(p) => matches!(p.as_ref(), VerifyAtomicExceptEqualityFactResult::Success(p) if matches!(&p.searched_proof, AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(k) if k.cite_fact_id == guard_id)),
        _ => false,
    }));
}

#[test]
fn builder_projection_retains_selected_alias_path_and_each_actual_wd() {
    let result = execute("have A set = {x R: x >= 0}\nforall y A:\n    y >= 0\n");
    assert!(result.success);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &result.statement_results[1] else {
        panic!("forall statement")
    };
    let VerifyFactResult::ForallFact(p) = &p.verify_result else {
        panic!("forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = p.as_ref()
    else {
        panic!("actual introduction")
    };
    let store = &p.introduced_params.defined_params.store_and_infer_results[0];
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &store.infer else {
        panic!("membership inference")
    };
    let captured = rules
        .iter()
        .find_map(|r| {
            if let InferInFactResult::SetBuilder(p) = r {
                Some(p)
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(captured.steps.len(), 1);
    let step = &captured.steps[0];
    assert_eq!(step.source_membership.fact_id, store.primary_fact_id());
    assert_eq!(step.equality_path.len(), 1);
    assert!(!step.template_expansion);
    assert_eq!(step.projections.len(), 2);
    assert!(step.stored_conclusions().all(|p| matches!(
        &p.store,
        crate::store_fact_and_infer::StoreFactResult::AtomicFact(_)
    )));
}

#[test]
fn builder_predicate_cannot_form_an_unguarded_reciprocal() {
    let result = execute("have A set = {x R: 1 / x > 0}\n");
    assert!(!result.success);
    assert!(result.session_error.is_none());
}
