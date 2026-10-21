use crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof;
use crate::execute::execute_fact_stmt::known_tuple::{
    KnownCartesianTupleProof, KnownTupleShapeProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

const SOURCE: &str =
    "forall coordinate_point cart(R, R):\n    coordinate_point(1) = coordinate_point(1)\n";

const VALUE_SOURCE: &str = "have p cart(R, R) = (1, 2)\np(1) = 1\n";

fn value_shape(
    result: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_fact_stmt::known_tuple::KnownTupleValueProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[1]
    else {
        panic!("coordinate fact")
    };
    let equality = super::equality_proof_mut(&mut fact.verify_result);
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(proof),
        ..
    } = &mut equality.well_defined_proof.left
    else {
        panic!("coordinate call WD")
    };
    let Some(FnObjDomainFnSetEvidence::FiniteFunction(finite)) = &mut proof.domain_fn_set else {
        panic!("finite call")
    };
    let KnownTupleShapeProof::TupleEquality(shape) = &mut finite.source else {
        panic!("retained tuple value")
    };
    shape
}

#[test]
fn finite_tuple_value_uses_its_singleton_contract_and_original_equality() {
    let (mut result, compiler) = super::execute(VALUE_SOURCE);
    assert_eq!(value_shape(&mut result).value.args.len(), 2);
    assert!(compiler
        .compile_run(&result, "tuple_value_call")
        .unwrap()
        .contains("Litex.tupleInSingletonCart"));
}

#[test]
fn finite_tuple_value_rejects_a_changed_equality_citation() {
    let (mut result, compiler) = super::execute(VALUE_SOURCE);
    value_shape(&mut result).tuple_equal.path[0].2 = FactId::new(u64::MAX);
    compiler
        .compile_run(&result, "forged_tuple_value")
        .expect_err("the singleton contract must use the original tuple equality");
}

fn finite(statement: &mut ExecStmtResult) -> &mut FiniteFunctionSignatureProof {
    let fact = super::forall_proof_mut(statement);
    let equality = super::equality_proof_mut(&mut fact.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(proof),
        ..
    } = &mut equality.well_defined_proof.left
    else {
        panic!("original finite coordinate WD")
    };
    let Some(FnObjDomainFnSetEvidence::FiniteFunction(finite)) = &mut proof.domain_fn_set else {
        panic!("original finite function signature")
    };
    finite
}

fn shape(statement: &mut ExecStmtResult) -> &mut KnownCartesianTupleProof {
    let KnownTupleShapeProof::CartesianMembership(shape) = &mut finite(statement).source else {
        panic!("original Cartesian membership")
    };
    shape
}

#[test]
fn finite_coordinate_uses_its_exact_citation_for_empty_equality_paths() {
    let (mut result, compiler) = super::execute(SOURCE);
    let captured = shape(&mut result.statement_results[0]);
    assert!(captured.subject_equal.path.is_empty());
    assert!(captured.carrier_equal.path.is_empty());
    let id = captured.membership.fact_id;
    let output = compiler
        .compile_run(&result, "coordinate_citation")
        .unwrap();
    assert!(output.contains(&format!(")) h_{} (by change M.mem", id.value())));
    assert!(output.contains("Litex.Same _object_w") && output.contains(" _object_h"));
    assert!(!output.contains("Litex.indexSetMemberOfClosedRange"));
}

#[test]
fn finite_coordinate_still_rejects_changed_membership_under_empty_paths() {
    let (mut result, compiler) = super::execute(SOURCE);
    shape(&mut result.statement_results[0]).membership.set = Obj::StandardSet(StandardSet::R);
    let error = compiler
        .compile_run(&result, "changed_cart_member")
        .unwrap_err();
    assert_eq!(error.route, "FiniteFunction/MembershipCitation");
}

#[test]
fn finite_coordinate_still_requires_the_original_carrier_wd() {
    let (mut result, compiler) = super::execute(SOURCE);
    let captured = finite(&mut result.statement_results[0]);
    let KnownTupleShapeProof::CartesianMembership(shape) = &mut captured.source else {
        panic!("original Cartesian membership")
    };
    shape.cart.args[0] = Box::new(Obj::StandardSet(StandardSet::Z));
    captured.signature.ret_set = Box::new(Obj::SetOperator(SetOperator::Union(Union {
        left: Box::new(Obj::StandardSet(StandardSet::Z)),
        right: Box::new(Obj::StandardSet(StandardSet::R)),
    })));
    let error = compiler
        .compile_run(&result, "changed_cart_endpoint")
        .unwrap_err();
    // The changed carrier has no original constructor in this scope; the
    // compiler must reject it before sharing the unchanged member citation.
    assert_eq!(error.route, "WD/Producer");
}
