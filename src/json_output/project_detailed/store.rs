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
    let Some(infer) = &node.infer else {
        return object_for(runtime, entries);
    };
    let prop_rules = project_prop_definition_infer(infer, runtime);
    if !prop_rules.is_empty() {
        entries.push(("prop_definition_rules", JsonValue::Array(prop_rules)));
    }
    let signed_rules = project_signed_standard_set_infer(infer, runtime);
    if !signed_rules.is_empty() {
        entries.push(("signed_standard_set_rules", JsonValue::Array(signed_rules)));
    }
    let cancellation_rules = project_cancellation_infer(infer, runtime);
    if !cancellation_rules.is_empty() {
        entries.push(("cancellation_rules", JsonValue::Array(cancellation_rules)));
    }
    let order_rules = project_conditional_order_infer(infer, runtime);
    if !order_rules.is_empty() {
        entries.push(("conditional_order_rules", JsonValue::Array(order_rules)));
    }
    if let InferFactResult::ChainFact(chain) = infer {
        entries.push((
            "chain_adjacent_infers",
            JsonValue::Array(
                chain
                    .adjacent_infers
                    .iter()
                    .map(|edge| {
                        object_for(
                            runtime,
                            vec![
                                ("edge_index", JsonValue::Number(edge.edge_index as f64)),
                                ("fact_id", string(edge.fact.fact_id().to_string())),
                                ("fact", string(edge.fact.readable_string())),
                            ],
                        )
                    })
                    .collect(),
            ),
        ));
        entries.push((
            "chain_transitive_closures",
            JsonValue::Array(
                chain
                    .transitive_closures
                    .iter()
                    .map(|closure| {
                        object_for(
                            runtime,
                            vec![
                                (
                                    "start_object_index",
                                    JsonValue::Number(closure.start_object_index as f64),
                                ),
                                (
                                    "end_object_index",
                                    JsonValue::Number(closure.end_object_index as f64),
                                ),
                                (
                                    "well_defined",
                                    super::wd::project_fact_wd_proof(
                                        &closure.derived.well_defined,
                                        runtime,
                                    ),
                                ),
                                ("store", project_store(&closure.derived.store, runtime)),
                            ],
                        )
                    })
                    .collect(),
            ),
        ));
    }
    object_for(runtime, entries)
}

fn project_conditional_order_infer(infer: &InferFactResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic = match infer {
        InferFactResult::AtomicFact(atomic) => vec![atomic],
        InferFactResult::AndFact(and) => and.components.iter().collect(),
        InferFactResult::ChainFact(chain) => chain
            .adjacent_infers
            .iter()
            .map(|edge| &edge.infer)
            .collect(),
        _ => return Vec::new(),
    };
    let mut result = Vec::new();
    for atomic in atomic {
        let InferAtomicFactResult::ExceptEquality(rules) = atomic else {
            continue;
        };
        for rule in rules {
            let (name, source, integer, bound, derived) = match rule {
                InferAtomicExceptEqualityResult::WeakIntegerLowerBoundInN(proof) => (
                    "WeakIntegerLowerBoundInN",
                    proof.source_fact_id,
                    Some(&proof.integer_proof),
                    &proof.bound_nonnegative_proof,
                    &proof.derived,
                ),
                InferAtomicExceptEqualityResult::StrictLowerBoundPositive(proof) => (
                    "StrictLowerBoundPositive",
                    proof.source_fact_id,
                    None,
                    &proof.bound_nonnegative_proof,
                    &proof.derived,
                ),
                _ => continue,
            };
            let mut fields = vec![
                ("rule", string(name)),
                ("source", fact_id_entry(runtime, source)),
            ];
            if let Some(integer) = integer {
                fields.push((
                    "integer_proof",
                    super::verify::project_verify_fact(integer, runtime),
                ));
            }
            fields.extend([
                (
                    "bound_nonnegative_proof",
                    super::verify::project_verify_fact(bound, runtime),
                ),
                (
                    "well_defined",
                    super::wd::project_fact_wd_proof(&derived.well_defined, runtime),
                ),
                ("store", project_store(&derived.store, runtime)),
            ]);
            result.push(object_for(runtime, fields));
        }
    }
    result
}

fn project_prop_definition_infer(infer: &InferFactResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic = match infer {
        InferFactResult::AtomicFact(atomic) => vec![atomic],
        InferFactResult::AndFact(and) => and.components.iter().collect(),
        InferFactResult::ChainFact(chain) => chain
            .adjacent_infers
            .iter()
            .map(|edge| &edge.infer)
            .collect(),
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
                                            ("store", project_store(&result.store, runtime)),
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
        InferFactResult::ChainFact(chain) => chain
            .adjacent_infers
            .iter()
            .map(|edge| &edge.infer)
            .collect(),
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
                                            ("store", project_store(&captured.store, runtime)),
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
                rules.extend(project_cancellation_atomic(&atomic.infer, runtime));
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
                                ("store", project_store(&r.derived.store, runtime)),
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
    result: &crate::store_fact_and_infer::StoreInferredFactResult,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "well_defined",
                super::wd::project_fact_wd_proof(&result.well_defined, runtime),
            ),
            ("store", project_store(&result.store, runtime)),
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

fn project_store(store: &StoreFactResult, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![(
            "stores",
            JsonValue::Array(
                store
                    .stored_fact_ids()
                    .into_iter()
                    .map(|id| fact_id_entry(runtime, id))
                    .collect(),
            ),
        )],
    )
}
