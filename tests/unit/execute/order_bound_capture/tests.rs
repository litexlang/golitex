use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::*;
use crate::prelude::*;
use crate::store_fact_and_infer::InferLessEqualFactResult;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferResult, StoreInferredFactResult};

fn atomic(captured: &StoreInferredFactResult) -> &AtomicFact {
    let StoreFactResult::AtomicFact(stored) = &captured.store else {
        panic!("actual inferred atomic store")
    };
    &stored.fact
}

#[test]
fn bounded_chain_filter_retains_weak_natural_sign_and_closure_formation() {
    let source = "have Interval set = {x R: 0 <= x <= 1}\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let result =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed)
            .run_litex_code(source)
            .unwrap();
    assert!(result.success && result.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(declaration)),
    )) = &result.statement_results[0]
    else {
        panic!("actual bounded-set declaration")
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SetBuilder(builder)),
        ..
    }) = (&declaration.equal_to_well_defined[0])
        .as_detailed_success()
        .unwrap()
    else {
        panic!("actual set-builder formation")
    };
    let [assumed] = builder.assumed_facts.as_slice() else {
        panic!("the original ordered chain filter")
    };
    let StoreFactResult::ChainFact(stored) = &assumed.store_and_infer.store else {
        panic!("original adjacent stores")
    };
    let Some(InferResult::ChainFact(inferred)) = &assumed.store_and_infer.infer else {
        panic!("original chain inference")
    };
    assert_eq!(stored.adjacent.len(), 2);
    assert_eq!(inferred.adjacent_infers.len(), 2);
    let InferAtomicFactResult::LessEqualFact(rules) = &inferred.adjacent_infers[1].infer else {
        panic!("upper edge inference")
    };
    let weak = rules
        .iter()
        .find_map(|rule| match rule {
            InferLessEqualFactResult::WeakIntegerLowerBoundInN(proof) => Some(proof),
        })
        .expect("x <= 1 derives 1 in N from the earlier 0 <= x certificate");
    // Chain storage and its subsequent atomic inference have distinct source IDs.
    assert_eq!(
        weak.source_fact_id,
        inferred.adjacent_infers[1].fact.fact_id()
    );
    let VerifyFactResult::AtomicExceptEquality(bound) = &weak.bound_nonnegative_proof else {
        panic!("earlier nonnegative bound certificate")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(bound) = bound.as_ref() else {
        panic!("proved nonnegative bound")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) = &bound.searched_proof
    else {
        panic!("actual earlier chain component citation")
    };
    assert_eq!(citation.cite_fact_id, stored.adjacent[0].fact_id);
    assert!(!weak.integer_proof.is_failed());
    let AtomicFact::InFact(natural) = atomic(&weak.derived) else {
        panic!("derived natural member")
    };
    assert_eq!(natural.element.readable_string(), "1");
    assert_eq!(natural.set, Obj::StandardSet(StandardSet::N));
    assert_eq!(
        weak.derived.stored_fact_ids().len(),
        1,
        "natural membership is stored without a new sign inference"
    );

    let [closure] = inferred.transitive_closures.as_slice() else {
        panic!("original endpoint closure")
    };
    assert_eq!(closure.premise_edge_indexes, [0, 1]);
    assert_eq!(atomic(&closure.derived).readable_string(), "0 <= 1");
    let ids = assumed.store_and_infer.stored_fact_ids();
    for captured in [&weak.derived, &closure.derived] {
        assert!(ids.contains(&captured.store.primary_fact_id()));
    }
}
