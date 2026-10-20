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

#[test]
fn returned_cart_call_wd_lets_only_reuse_emitted_original_children() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut result, _) = super::execute(SOURCE);
    let fact = super::forall_proof_mut(&mut result.statement_results[1]);
    let equality = super::equality_proof_mut(&mut fact.proved_then_facts[0].verify_result);
    let owner = &equality.well_defined_proof.left;
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = owner
    else {
        panic!("original call WD")
    };
    let first = call.child_obj_well_defined[0].as_ref();
    let second = call.child_obj_well_defined[1].as_ref();
    let before = SourcePosition::new(None, SourceOwner::WDLocals(owner, 0), 0);
    assert!(before.bound_wd_child(first).is_none());
    assert!(before.bound_object_child(second.obj()).is_none());
    let after_first = SourcePosition::new(None, SourceOwner::WDLocals(owner, 1), 1);
    assert!(after_first.bound_wd_child(first).is_some());
    assert!(after_first.bound_object_child(first.obj()).is_some());
    assert!(after_first.bound_wd_child(second).is_none());
    assert!(after_first.bound_object_child(second.obj()).is_none());
    // The enclosing constructor has not been emitted as one of its children.
    assert!(after_first.bound_wd_child(owner).is_none());
    let outside = SourcePosition::new(None, SourceOwner::WD(owner), usize::MAX);
    assert!(outside.bound_wd_child(first).is_none());
    let requirement = &call.requirement_fact_verified[0];
    let before_requirements = SourcePosition::new(
        None,
        SourceOwner::WDLocals(owner, call.child_obj_well_defined.len()),
        0,
    );
    assert!(!before_requirements.has_bound_verify(requirement));
    let after_requirement = SourcePosition::new(
        None,
        SourceOwner::WDLocals(owner, call.child_obj_well_defined.len() + 1),
        0,
    );
    assert!(after_requirement.has_bound_verify(requirement));
    assert!(!after_requirement.has_bound_verify(&call.requirement_fact_verified[1]));
    assert!(!outside.has_bound_verify(requirement));
}
