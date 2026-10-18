use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    by_fn_application::{
        normalize_function_body::{AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof},
        EqualitySearchProofByFnApplicationObjectDefinition,
    },
    EqualitySearchProofByObjectDefinition,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

// The G1 tracer keeps the actual geometric argument carriers and equality chain.
const DOT_SYMMETRIC: &str = "have fn dot(u, v cart(R, R)) R = u(1) * v(1) + u(2) * v(2)\n\nthm dot_symmetric:\n    ? forall u, v cart(R, R):\n        dot(u, v) = dot(v, u)\n    dot(u, v) = u(1) * v(1) + u(2) * v(2) = v(1) * u(1) + v(2) * u(2) = dot(v, u)\n";

fn expansion(
    result: &mut RunLitexCodeResult,
    edge: usize,
) -> &mut AnonymousFunctionBodyExpansionProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &mut result.statement_results[1]
    else {
        panic!("the original named geometry theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("the original universal theorem body")
    };
    let step = super::fact_statement_mut(&mut body.proof_steps[0]);
    let VerifyFactResult::ChainFact(chain) = &mut step.verify_result else {
        panic!("the original equality chain")
    };
    let VerifyChainFactResult::Success(chain) = chain.as_mut() else {
        panic!("the accepted equality chain")
    };
    let equal = super::equality_proof_mut(&mut chain.adjacent[edge]);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(proof),
        ),
    ) = &mut equal.searched_proof
    else {
        panic!("the recorded formula-body normalization")
    };
    let FunctionBodyExpansionProof::Anonymous(expansion) = &mut proof.normalization.expansions[0]
    else {
        panic!("the selected anonymous formula expansion")
    };
    expansion
}

fn selected_call(
    expansion: &mut AnonymousFunctionBodyExpansionProof,
) -> &mut FnObjObjWellDefinedProof {
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = &mut expansion.body_application_well_defined
    else {
        panic!("the original selected literal call WD")
    };
    assert_eq!(call.child_obj_well_defined.len(), 3);
    assert_eq!(call.requirement_fact_verified.len(), 2);
    assert!(matches!(
        call.child_obj_well_defined[0].as_ref(),
        ObjWellDefinedProof::ByKnown { .. }
    ));
    call
}

#[test]
fn cached_formula_head_keeps_the_original_selected_wd_id_check() {
    for edge in [0, 2] {
        let (mut result, compiler) = super::execute(DOT_SYMMETRIC);
        let selected = selected_call(expansion(&mut result, edge));
        let ObjWellDefinedProof::ByKnown { wd_id, .. } =
            selected.child_obj_well_defined[0].as_mut()
        else {
            unreachable!()
        };
        *wd_id = WellDefinednessId::new(u64::MAX);
        super::phase2_rejected(
            &result,
            &compiler,
            "a named object cannot repair a corrupted original cached WD citation",
            &["WdId/Resolution", "WD/ByKnown"],
        );
    }
}

#[test]
fn cached_formula_head_cannot_replace_the_selected_call_requirements() {
    for edge in [0, 2] {
        let (mut result, compiler) = super::execute(DOT_SYMMETRIC);
        selected_call(expansion(&mut result, edge))
            .requirement_fact_verified
            .pop();
        super::phase2_rejected(
            &result,
            &compiler,
            "sharing the cached head must retain every selected parameter membership",
            &["WD/FnObj/StageArity"],
        );
    }
}
