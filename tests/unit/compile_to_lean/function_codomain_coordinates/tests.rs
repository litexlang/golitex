use crate::execute::execute_fact_stmt::known_tuple::{
    KnownFunctionCartesianTupleProof, KnownTupleShapeProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,
    InFactSearchProofByKnownSpecialProperty,
};
use crate::prelude::*;

// The accepted dot expansion on vector-valued arguments. Keep this source
// inline so the public test does not depend on the local scripts workspace.
const SOURCE: &str = "have fn vec(A, B cart(R, R)) cart(R, R) = (B(1) - A(1), B(2) - A(2))\nhave fn dot(u, v cart(R, R)) R = u(1) * v(1) + u(2) * v(2)\nforall nested_u, nested_v cart(R, R):\n    dot(vec(nested_u, nested_v), vec(nested_u, nested_v)) = vec(nested_u, nested_v)(1) * vec(nested_u, nested_v)(1) + vec(nested_u, nested_v)(2) * vec(nested_u, nested_v)(2)\n";

fn shape(statement: &mut ExecStmtResult) -> &mut KnownFunctionCartesianTupleProof {
    let forall = super::forall_proof_mut(statement);
    let equality = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Add(add),
            ),
        ..
    } = &mut equality.well_defined_proof.right
    else {
        panic!("original dot expansion's right-hand sum")
    };
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Mul(mul),
            ),
        ..
    } = add.child_obj_well_defined[0].as_mut()
    else {
        panic!("original first coordinate product")
    };
    let complex = super::atomic_proof_mut(&mut mul.requirement_fact_verified[0]);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::StandardSetSubsetMembership(inclusion),
        ),
    ) = &mut complex.searched_proof
    else {
        panic!("original real-to-complex coordinate inclusion")
    };
    let real = super::atomic_proof_mut(&mut inclusion.source_membership_proof);
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::TupleCoordinate(coordinate),
        ),
    ) = &mut real.searched_proof
    else {
        panic!("original real coordinate membership")
    };
    let KnownTupleShapeProof::FunctionCodomain(shape) = &mut coordinate.shape else {
        panic!("original function-codomain shape")
    };
    shape
}

#[test]
fn function_codomain_coordinates_replay_the_original_signature_evidence() {
    let (mut result, compiler) = super::execute(SOURCE);
    let captured = shape(&mut result.statement_results[2]);
    assert!(captured.function_equal.path.is_empty());
    assert!(captured.carrier_equal.path.is_empty());
    assert!(!captured.membership_proof.signature_uses.is_empty());
    assert_ne!(
        captured.membership.fact_id, captured.membership_proof.cite_property_fact_id,
        "the internal membership goal is distinct from its published signature"
    );
    compiler
        .compile_run(&result, "function_codomain_coordinates")
        .expect("the original codomain proof establishes the vector's coordinate carrier");
}

#[test]
fn function_codomain_coordinates_reject_missing_signature_uses() {
    let (mut result, compiler) = super::execute(SOURCE);
    shape(&mut result.statement_results[2])
        .membership_proof
        .signature_uses
        .clear();
    let error = compiler
        .compile_run(&result, "function_codomain_missing_signatures")
        .unwrap_err();
    assert_eq!(error.route, "FunctionReturn/SelectedSignature");
}

#[test]
fn function_codomain_coordinates_reject_an_unpublished_signature_citation() {
    let (mut result, compiler) = super::execute(SOURCE);
    let captured = shape(&mut result.statement_results[2]);
    captured.membership_proof.cite_property_fact_id = captured.membership.fact_id;
    let error = compiler
        .compile_run(&result, "function_codomain_unpublished_signature")
        .unwrap_err();
    assert_eq!(error.route, "FactId/Resolution");
}

#[test]
fn function_codomain_coordinates_reject_a_changed_return_carrier() {
    let (mut result, compiler) = super::execute(SOURCE);
    shape(&mut result.statement_results[2]).membership.set = Obj::StandardSet(StandardSet::R);
    let error = compiler
        .compile_run(&result, "function_codomain_changed_carrier")
        .unwrap_err();
    assert_eq!(error.route, "FunctionReturn/ReturnSetMatch");
}
