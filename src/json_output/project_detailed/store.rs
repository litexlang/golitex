//! Store / infer helpers for Detailed projection (`local_env` omitted).

use crate::execute::StoreHaveObjAndInferResult;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferEqualityResult, InferFactResult,
};

pub(super) fn project_verify_facts(facts: &[VerifyFactResult], runtime: &Runtime) -> JsonValue {
    JsonValue::Array(
        facts
            .iter()
            .map(|f| super::verify::project_verify_fact(f, runtime))
            .collect(),
    )
}

pub(super) fn fact_id_entry(runtime: &Runtime, fact_id: FactId) -> JsonValue {
    let mut entries = vec![("fact_id", string(fact_id.to_string()))];
    if let Some(fact) = runtime.fact_by_id_in_stack(fact_id) {
        entries.push(("fact", string(fact.readable_string())));
    }
    object_for(runtime, entries)
}

// Detailed store/infer: keep fact_id + readable text. No search_trace (T1).
pub(super) fn project_store_and_infer(
    node: &StoreFactAndInferResult,
    runtime: &Runtime,
) -> JsonValue {
    let store_ids = node.store.stored_fact_ids();
    let all_ids = node.stored_fact_ids();
    let stores: Vec<JsonValue> = store_ids
        .iter()
        .copied()
        .map(|id| fact_id_entry(runtime, id))
        .collect();
    let infers: Vec<JsonValue> = all_ids
        .into_iter()
        .filter(|id| !store_ids.contains(id))
        .map(|id| fact_id_entry(runtime, id))
        .collect();
    let mut entries = vec![
        ("stores", JsonValue::Array(stores)),
        ("infers", JsonValue::Array(infers)),
    ];
    let prop_rules = project_prop_definition_infer(&node.infer, runtime);
    if !prop_rules.is_empty() {
        entries.push(("prop_definition_rules", JsonValue::Array(prop_rules)));
    }
    let signed_rules = project_signed_standard_set_infer(&node.infer, runtime);
    if !signed_rules.is_empty() {
        entries.push(("signed_standard_set_rules", JsonValue::Array(signed_rules)));
    }
    let cancellation_rules = project_cancellation_infer(&node.infer, runtime);
    if !cancellation_rules.is_empty() {
        entries.push(("cancellation_rules", JsonValue::Array(cancellation_rules)));
    }
    object_for(runtime, entries)
}

fn project_prop_definition_infer(infer: &InferFactResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic = match infer {
        InferFactResult::AtomicFact(atomic) => vec![atomic],
        InferFactResult::AndFact(and) => and.components.iter().collect(),
        InferFactResult::ChainFact(chain) => chain.adjacent_infers.iter().collect(),
        InferFactResult::OrFact(_)
        | InferFactResult::ExistShapedFact(_)
        | InferFactResult::NotForallFact(_)
        | InferFactResult::ForallFact(_)
        | InferFactResult::ForallFactWithIff(_) => return Vec::new(),
    };
    let mut rules = Vec::new();
    for atomic in atomic {
        let InferAtomicFactResult::ExceptEquality(infer) = atomic else {
            continue;
        };
        for rule in infer {
            let (name, derived) = match rule {
                InferAtomicExceptEqualityResult::NormalAtomicParamTypes(result) => {
                    ("NormalAtomicParamTypes", &result.derived)
                }
                InferAtomicExceptEqualityResult::NormalAtomicExpandDefinition(result) => {
                    ("NormalAtomicExpandDefinition", &result.derived)
                }
                _ => continue,
            };
            rules.push(object_for(
                runtime,
                vec![
                    ("rule", string(name)),
                    (
                        "derived",
                        JsonValue::Array(
                            derived
                                .iter()
                                .map(|result| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "well_defined",
                                                super::wd::project_fact_wd_proof(
                                                    &result.well_defined,
                                                    runtime,
                                                ),
                                            ),
                                            (
                                                "store_and_infer",
                                                project_store_and_infer(
                                                    &result.store_and_infer,
                                                    runtime,
                                                ),
                                            ),
                                        ],
                                    )
                                })
                                .collect(),
                        ),
                    ),
                ],
            ));
        }
    }
    rules
}

fn project_signed_standard_set_infer(infer: &InferFactResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic = match infer {
        InferFactResult::AtomicFact(atomic) => vec![atomic],
        InferFactResult::AndFact(and) => and.components.iter().collect(),
        InferFactResult::ChainFact(chain) => chain.adjacent_infers.iter().collect(),
        InferFactResult::OrFact(_)
        | InferFactResult::ExistShapedFact(_)
        | InferFactResult::NotForallFact(_)
        | InferFactResult::ForallFact(_)
        | InferFactResult::ForallFactWithIff(_) => return Vec::new(),
    };
    let mut rules = Vec::new();
    for atomic in atomic {
        let InferAtomicFactResult::ExceptEquality(infer) = atomic else {
            continue;
        };
        for rule in infer {
            let InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(proof) = rule else {
                continue;
            };
            rules.push(object_for(
                runtime,
                vec![
                    ("rule", string("InFactSignedStandardSetSign")),
                    (
                        "derived",
                        JsonValue::Array(
                            proof
                                .derived
                                .iter()
                                .map(|captured| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "well_defined",
                                                super::wd::project_fact_wd_proof(
                                                    &captured.well_defined,
                                                    runtime,
                                                ),
                                            ),
                                            (
                                                "store_and_infer",
                                                project_store_and_infer(
                                                    &captured.store_and_infer,
                                                    runtime,
                                                ),
                                            ),
                                        ],
                                    )
                                })
                                .collect(),
                        ),
                    ),
                ],
            ));
        }
    }
    rules
}

fn project_cancellation_infer(infer: &InferFactResult, runtime: &Runtime) -> Vec<JsonValue> {
    let mut rules = Vec::new();
    match infer {
        InferFactResult::AtomicFact(atomic) => {
            rules.extend(project_cancellation_atomic(atomic, runtime))
        }
        InferFactResult::AndFact(and) => {
            for atomic in &and.components {
                rules.extend(project_cancellation_atomic(atomic, runtime));
            }
        }
        InferFactResult::ChainFact(chain) => {
            for atomic in &chain.adjacent_infers {
                rules.extend(project_cancellation_atomic(atomic, runtime));
            }
            for closure in &chain.transitive_closures {
                rules.extend(project_cancellation_infer(&closure.derived.infer, runtime));
            }
        }
        InferFactResult::OrFact(_)
        | InferFactResult::ExistShapedFact(_)
        | InferFactResult::NotForallFact(_)
        | InferFactResult::ForallFact(_)
        | InferFactResult::ForallFactWithIff(_) => {}
    }
    rules
}

fn project_cancellation_atomic(infer: &InferAtomicFactResult, runtime: &Runtime) -> Vec<JsonValue> {
    let InferAtomicFactResult::EqualFact(infer) = infer else {
        return Vec::new();
    };
    let mut rules = Vec::new();
    for rule in infer {
        match rule {
            InferEqualityResult::AdditiveCancellation(r) => rules.push(object_for(
                runtime,
                vec![
                    ("rule", string("AdditiveCancellation")),
                    ("source", fact_id_entry(runtime, r.source_fact_id)),
                    ("common_operand", string(r.common_operand.readable_string())),
                    (
                        "left_in_c_proof",
                        super::verify::project_verify_fact(&r.left_in_c_proof, runtime),
                    ),
                    (
                        "right_in_c_proof",
                        super::verify::project_verify_fact(&r.right_in_c_proof, runtime),
                    ),
                    (
                        "common_in_c_proof",
                        super::verify::project_verify_fact(&r.common_in_c_proof, runtime),
                    ),
                    (
                        "derived",
                        object_for(
                            runtime,
                            vec![
                                (
                                    "well_defined",
                                    super::wd::project_fact_wd_proof(
                                        &r.derived.well_defined,
                                        runtime,
                                    ),
                                ),
                                (
                                    "store_and_infer",
                                    project_store_and_infer(&r.derived.store_and_infer, runtime),
                                ),
                            ],
                        ),
                    ),
                ],
            )),
            InferEqualityResult::NonzeroFactorCancellation(r) => rules.push(object_for(
                runtime,
                vec![
                    ("rule", string("NonzeroFactorCancellation")),
                    ("source", fact_id_entry(runtime, r.source_fact_id)),
                    ("common_operand", string(r.common_operand.readable_string())),
                    (
                        "left_in_c_proof",
                        super::verify::project_verify_fact(&r.left_in_c_proof, runtime),
                    ),
                    (
                        "right_in_c_proof",
                        super::verify::project_verify_fact(&r.right_in_c_proof, runtime),
                    ),
                    (
                        "common_in_c_proof",
                        super::verify::project_verify_fact(&r.common_in_c_proof, runtime),
                    ),
                    (
                        "factor_nonzero_proof",
                        super::verify::project_verify_fact(&r.factor_nonzero_proof, runtime),
                    ),
                    ("derived", project_inferred_store(&r.derived, runtime)),
                ],
            )),
            InferEqualityResult::SubtractiveCancellation(r) => rules.push(object_for(
                runtime,
                vec![
                    ("rule", string("SubtractiveCancellation")),
                    ("source", fact_id_entry(runtime, r.source_fact_id)),
                    ("common_operand", string(r.common_operand.readable_string())),
                    (
                        "left_in_c_proof",
                        super::verify::project_verify_fact(&r.left_in_c_proof, runtime),
                    ),
                    (
                        "right_in_c_proof",
                        super::verify::project_verify_fact(&r.right_in_c_proof, runtime),
                    ),
                    (
                        "common_in_c_proof",
                        super::verify::project_verify_fact(&r.common_in_c_proof, runtime),
                    ),
                    ("derived", project_inferred_store(&r.derived, runtime)),
                ],
            )),
            InferEqualityResult::CommonDenominatorCancellation(r) => rules.push(object_for(
                runtime,
                vec![
                    ("rule", string("CommonDenominatorCancellation")),
                    ("source", fact_id_entry(runtime, r.source_fact_id)),
                    ("common_operand", string(r.common_operand.readable_string())),
                    (
                        "left_in_c_proof",
                        super::verify::project_verify_fact(&r.left_in_c_proof, runtime),
                    ),
                    (
                        "right_in_c_proof",
                        super::verify::project_verify_fact(&r.right_in_c_proof, runtime),
                    ),
                    (
                        "common_in_c_proof",
                        super::verify::project_verify_fact(&r.common_in_c_proof, runtime),
                    ),
                    (
                        "denominator_nonzero_proof",
                        super::verify::project_verify_fact(&r.denominator_nonzero_proof, runtime),
                    ),
                    ("derived", project_inferred_store(&r.derived, runtime)),
                ],
            )),
            InferEqualityResult::NonzeroNumeratorCancellation(r) => rules.push(object_for(
                runtime,
                vec![
                    ("rule", string("NonzeroNumeratorCancellation")),
                    ("source", fact_id_entry(runtime, r.source_fact_id)),
                    ("common_operand", string(r.common_operand.readable_string())),
                    (
                        "left_in_c_proof",
                        super::verify::project_verify_fact(&r.left_in_c_proof, runtime),
                    ),
                    (
                        "right_in_c_proof",
                        super::verify::project_verify_fact(&r.right_in_c_proof, runtime),
                    ),
                    (
                        "common_in_c_proof",
                        super::verify::project_verify_fact(&r.common_in_c_proof, runtime),
                    ),
                    (
                        "numerator_nonzero_proof",
                        super::verify::project_verify_fact(&r.numerator_nonzero_proof, runtime),
                    ),
                    (
                        "left_denominator_nonzero_proof",
                        super::verify::project_verify_fact(
                            &r.left_denominator_nonzero_proof,
                            runtime,
                        ),
                    ),
                    (
                        "right_denominator_nonzero_proof",
                        super::verify::project_verify_fact(
                            &r.right_denominator_nonzero_proof,
                            runtime,
                        ),
                    ),
                    ("derived", project_inferred_store(&r.derived, runtime)),
                ],
            )),
            InferEqualityResult::PositiveRealPower(_) => {}
        }
    }
    rules
}

pub(super) fn project_have_store_ids(fact_ids: &[FactId], runtime: &Runtime) -> JsonValue {
    let stores: Vec<JsonValue> = fact_ids
        .iter()
        .copied()
        .map(|id| fact_id_entry(runtime, id))
        .collect();
    object_for(
        runtime,
        vec![
            ("stores", JsonValue::Array(stores)),
            ("infers", JsonValue::Array(Vec::new())),
        ],
    )
}

fn project_inferred_store(
    result: &crate::store_fact_and_infer::StoreInferredFactAndInferResult,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "well_defined",
                super::wd::project_fact_wd_proof(&result.well_defined, runtime),
            ),
            (
                "store_and_infer",
                project_store_and_infer(&result.store_and_infer, runtime),
            ),
        ],
    )
}

pub(super) fn project_have_store_and_infer(
    result: &StoreHaveObjAndInferResult,
    runtime: &Runtime,
) -> JsonValue {
    let stores = result
        .stored_fact_ids
        .iter()
        .copied()
        .map(|id| fact_id_entry(runtime, id))
        .collect();
    object_for(
        runtime,
        vec![
            ("stores", JsonValue::Array(stores)),
            ("infers", JsonValue::Array(Vec::new())),
            (
                "store_and_infer_results",
                JsonValue::Array(
                    result
                        .store_and_infer_results
                        .iter()
                        .map(|stored| project_store_and_infer(stored, runtime))
                        .collect(),
                ),
            ),
        ],
    )
}
