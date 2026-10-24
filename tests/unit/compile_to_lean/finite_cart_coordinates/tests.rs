use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

const SOURCE: &str =
    "forall coordinate_point cart(R, R):\n    coordinate_point(1) = coordinate_point(1)\n";

// Keep this fixture on the tuple-equality constructor. A declared Cartesian
// membership now publishes coordinate constructors before the queried call.
const VALUE_SOURCE: &str = "have p set = (1, 2)\np(1) = 1\n";

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

// Cartesian introductions now publish the coordinate constructors themselves.
// Inspect that original producer instead of assuming a later ByDef cache miss.
fn coordinates(
    statement: &mut ExecStmtResult,
) -> &mut crate::store_fact_and_infer::InferInFactCartCoordinatesResult {
    let fact = super::forall_proof_mut(statement);
    let store = std::rc::Rc::get_mut(
        &mut fact
            .introduced_params
            .defined_params
            .store_and_infer_results[0],
    )
    .expect("the original test introduction owns this result");
    let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
        crate::store_fact_and_infer::InferAtomicFactResult::InFact(rules),
    )) = &mut store.infer
    else {
        panic!("original Cartesian inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            crate::store_fact_and_infer::InferInFactResult::CartCoordinates(p) => Some(p),
            _ => None,
        })
        .expect("original coordinate producers")
}

#[test]
fn finite_coordinate_cache_uses_its_exact_original_membership_producer() {
    let (mut result, compiler) = super::execute(SOURCE);
    let projection_id = coordinates(&mut result.statement_results[0]).coordinates[0]
        .membership
        .primary_fact_id();
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let member_id = forall
        .introduced_params
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    let equality = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    if let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = &equality.well_defined_proof.left
    {
        let Some(FnObjDomainFnSetEvidence::FiniteFunction(finite)) = &call.domain_fn_set else {
            panic!("original finite constructor")
        };
        let KnownTupleShapeProof::CartesianMembership(source) = &finite.source else {
            panic!("direct Cartesian membership")
        };
        assert!(source.subject_equal.path.is_empty() && source.carrier_equal.path.is_empty());
        assert_eq!(source.membership.fact_id, member_id);
    }
    let output = compiler
        .compile_run(&result, "coordinate_citation")
        .unwrap();
    assert!(output.contains("Litex.cartCall _value_i"));
    assert!(output.contains(&format!("h_{} (by change M.mem", member_id.value())));
    assert!(output.contains(&format!("_object_h{}", projection_id.value())));
    assert!(!output.contains("Litex.indexSetMemberOfClosedRange"));
}

#[test]
fn finite_coordinate_cache_rejects_a_changed_original_membership_store() {
    let (mut result, compiler) = super::execute(SOURCE);
    let StoreFactResult::AtomicFact(stored) = &mut coordinates(&mut result.statement_results[0])
        .coordinates[0]
        .membership
        .store
    else {
        panic!("coordinate membership")
    };
    let AtomicFact::InFact(member) = &mut stored.fact else {
        panic!("membership")
    };
    member.set = Obj::StandardSet(StandardSet::Z);
    assert_eq!(
        compiler
            .compile_run(&result, "changed_coordinate_member")
            .unwrap_err()
            .route,
        "Store/Subject"
    );
}

#[test]
fn finite_coordinate_cache_still_requires_the_original_carrier_wd() {
    let (mut result, compiler) = super::execute(SOURCE);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let ParamTypeWellDefinedProof::Obj(ObjWellDefinedProof::ByDef {
        obj: Obj::ProductShape(ProductShape::Cart(cart)),
        ..
    }) = &mut forall.introduced_params.param_type_well_defined[0]
    else {
        panic!("original Cartesian carrier WD")
    };
    cart.args[0] = Box::new(Obj::StandardSet(StandardSet::Z));
    assert_eq!(
        compiler
            .compile_run(&result, "changed_cart_formation")
            .unwrap_err()
            .route,
        "WD/Subject"
    );
}
