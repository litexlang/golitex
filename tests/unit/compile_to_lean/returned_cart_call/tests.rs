use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

const SOURCE: &str = "have fn vec(A, B cart(R, R)) cart(R, R) = (B(1) - A(1), B(2) - A(2))\nforall p1, q1 cart(R, R):\n    vec(p1, q1)(1) = vec(p1, q1)(1)\n    vec(p1, q1)(2) = vec(p1, q1)(2)\n";

fn call(statement: &mut ExecStmtResult) -> &mut FnObjObjWellDefinedProof {
    let fact = super::forall_proof_mut(statement);
    let equality = super::equality_proof_mut(&mut fact.proved_then_facts[0].verify_result);
    match &mut equality.well_defined_proof.left {
        ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(proof),
            ..
        } => proof,
        _ => panic!("original two-layer call WD"),
    }
}

#[test]
fn returned_cart_call_replays_both_original_coordinate_domains() {
    let (result, compiler) = super::execute(SOURCE);
    let output = compiler
        .compile_run(&result, "returned_cart_coordinates")
        .expect("both one-based coordinates replay from the original call's ordered evidence");
    assert!(output.contains("exact M.real_subset_complex _ _litex_real_member"));
    assert!(output.contains("Litex.subInR"));
}

#[test]
fn returned_cart_call_rejects_a_missing_second_layer_child() {
    let (mut result, compiler) = super::execute(SOURCE);
    call(&mut result.statement_results[1])
        .child_obj_well_defined
        .pop();
    let error = compiler
        .compile_run(&result, "missing_coordinate_child")
        .unwrap_err();
    assert_eq!(error.route, "WD/FnObj/StageArity");
}

#[test]
fn returned_cart_call_rejects_a_missing_second_layer_domain() {
    let (mut result, compiler) = super::execute(SOURCE);
    call(&mut result.statement_results[1])
        .requirement_fact_verified
        .pop();
    let error = compiler
        .compile_run(&result, "missing_coordinate_domain")
        .unwrap_err();
    assert_eq!(error.route, "WD/FnObj/StageArity");
}

#[test]
fn returned_cart_call_rejects_reordered_layer_requirements() {
    let (mut result, compiler) = super::execute(SOURCE);
    call(&mut result.statement_results[1])
        .requirement_fact_verified
        .swap(0, 2);
    let error = compiler
        .compile_run(&result, "wrong_coordinate_domain")
        .unwrap_err();
    assert_eq!(error.route, "WD/FnObj/ParameterMembership");
}
