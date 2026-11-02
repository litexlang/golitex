use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

const SOURCE: &str =
    "forall coordinate_point cart(R, R):\n    coordinate_point(1) = coordinate_point(1)\n";

// Direct tuple equalities now own their coordinate constructors. Inspect the
// original inference instead of assuming a later call must build fresh WD.
const VALUE_SOURCE: &str = "have p set = (1, 2)\np(1) = 1\n";

fn value_projection(
    result: &mut RunLitexCodeResult,
) -> &mut crate::store_fact_and_infer::InferEqualFactTupleCoordinatesResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = &mut result.statement_results[0]
    else {
        panic!("original tuple declaration")
    };
    let seed = std::rc::Rc::get_mut(
        proof
            .store_and_infer_result
            .store_and_infer_results
            .last_mut()
            .unwrap(),
    )
    .unwrap();
    let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
        crate::store_fact_and_infer::InferAtomicFactResult::EqualFact(rules),
    )) = &mut seed.infer
    else {
        panic!("original equality inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            crate::store_fact_and_infer::InferEqualFactResult::TupleCoordinates(rule) => Some(rule),
            _ => None,
        })
        .expect("original tuple coordinate producer")
}

#[test]
fn finite_tuple_value_uses_its_singleton_contract_and_original_equality() {
    let (mut result, compiler) = super::execute(VALUE_SOURCE);
    assert_eq!(value_projection(&mut result).coordinates.len(), 2);
    assert!(compiler
        .compile_run(&result, "tuple_value_call")
        .unwrap()
        .contains("Litex.tupleInSingletonCart"));
}

#[test]
fn finite_tuple_value_rejects_a_changed_equality_citation() {
    let (mut result, compiler) = super::execute(VALUE_SOURCE);
    value_projection(&mut result).source_fact_id = FactId::new(u64::MAX);
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
    if let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = (&equality.well_defined_proof.detailed_ref().left)
        .as_detailed()
        .unwrap()
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
    let ParamTypeWellDefinedProof::Obj(wd) =
        &mut forall.introduced_params.param_type_well_defined[0]
    else {
        panic!("cartesian parameter WD");
    };
    let DetailedObjWellDefinedProof::ByDef {
        obj: Obj::ProductShape(ProductShape::Cart(cart)),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("cartesian parameter WD");
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
