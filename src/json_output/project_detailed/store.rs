//! Store / infer helpers for Detailed projection (`local_env` omitted).

use crate::execute::StoreHaveObjAndInferResult;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::prelude::*;
use crate::store_fact_and_infer::InferPositiveRealPowerPositivityResult;
use crate::store_fact_and_infer::StoreInferredFactResult;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferEqualFactResult, InferResult};
use crate::store_fact_and_infer::{
    InferGreaterEqualFactResult, InferGreaterFactResult, InferInFactResult,
    InferLessEqualFactResult, InferLessFactResult, InferNormalAtomicFactResult,
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
        (
            "formed_subjects",
            JsonValue::Array(
                node.formed_subjects
                    .iter()
                    .map(|subject| {
                        object_for(
                            runtime,
                            vec![
                                (
                                    "argument_index",
                                    JsonValue::Number(subject.argument_index as f64),
                                ),
                                ("wd_id", string(subject.wd_id.to_string())),
                            ],
                        )
                    })
                    .collect(),
            ),
        ),
        ("infers", JsonValue::Array(infers)),
    ];
    let Some(infer) = &node.infer else {
        return object_for(runtime, entries);
    };
    if let InferResult::AtomicFact(InferAtomicFactResult::InFact(rules)) = infer {
        let matrices: Vec<_> = rules
            .iter()
            .filter_map(|rule| {
                let InferInFactResult::MatrixExpand(proof) = rule else {
                    return None;
                };
                Some(object_for(
                    runtime,
                    vec![
                        ("source", fact_id_entry(runtime, proof.source_fact_id)),
                        (
                            "matrix_space",
                            string(
                                Obj::SetFormer(SetFormer::MatrixSet(proof.matrix_space.clone()))
                                    .readable_string(),
                            ),
                        ),
                        (
                            "carrier_equal",
                            super::searched::project_known_equality_path(
                                &proof.carrier_equal,
                                runtime,
                            ),
                        ),
                    ],
                ))
            })
            .collect();
        if !matrices.is_empty() {
            entries.push(("matrix_expansions", JsonValue::Array(matrices)));
        }
        let templates = rules
            .iter()
            .filter_map(|rule| {
                let InferInFactResult::Template(proof) = rule else {
                    return None;
                };
                Some(object_for(
                    runtime,
                    vec![
                        ("source", fact_id_entry(runtime, proof.source_fact_id)),
                        (
                            "expanded_memberships",
                            JsonValue::Array(
                                proof
                                    .expansions
                                    .iter()
                                    .map(|m| {
                                        string(
                                            Fact::AtomicFact(AtomicFact::InFact(m.clone()))
                                                .readable_string(),
                                        )
                                    })
                                    .collect(),
                            ),
                        ),
                        (
                            "native_conclusions",
                            JsonValue::Array(
                                proof
                                    .native_rules
                                    .iter()
                                    .flat_map(|r| r.stored_fact_ids())
                                    .map(|id| fact_id_entry(runtime, id))
                                    .collect(),
                            ),
                        ),
                    ],
                ))
            })
            .collect::<Vec<_>>();
        if !templates.is_empty() {
            entries.push(("template_membership_rules", JsonValue::Array(templates)));
        }
    }
    if let InferResult::AtomicFact(InferAtomicFactResult::InFact(rules)) = infer {
        let ranges = rules
            .iter()
            .filter_map(|r| {
                let InferInFactResult::FnRange(p) = r else {
                    return None;
                };
                Some(object_for(
                    runtime,
                    vec![
                        (
                            "signature_selection",
                            project_signature_selection(&p.signature_selection, runtime),
                        ),
                        (
                            "codomain_membership",
                            project_inferred_store(&p.codomain_membership, runtime),
                        ),
                        (
                            "preimage_witness",
                            p.preimage_witness
                                .as_ref()
                                .map(|p| project_inferred_store(p, runtime))
                                .unwrap_or(JsonValue::Null),
                        ),
                    ],
                ))
            })
            .collect::<Vec<_>>();
        if !ranges.is_empty() {
            entries.push(("function_range_rules", JsonValue::Array(ranges)));
        }
    }
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
    let positive_power_rules = project_positive_power_infer(infer, runtime);
    if !positive_power_rules.is_empty() {
        entries.push((
            "positive_real_power_rules",
            JsonValue::Array(positive_power_rules),
        ));
    }
    let order_rules = project_conditional_order_infer(infer, runtime);
    if !order_rules.is_empty() {
        entries.push(("conditional_order_rules", JsonValue::Array(order_rules)));
    }
    if let InferResult::ChainFact(chain) = infer {
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

fn project_conditional_order_infer(infer: &InferResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic = match infer {
        InferResult::AtomicFact(atomic) => vec![atomic],
        InferResult::AndFact(and) => and.components.iter().collect(),
        InferResult::ChainFact(chain) => chain
            .adjacent_infers
            .iter()
            .map(|edge| &edge.infer)
            .collect(),
        _ => return Vec::new(),
    };
    let mut result = Vec::new();
    let mut append = |name: &str,
                      source: FactId,
                      integer: Option<&VerifyFactResult>,
                      bound: &VerifyFactResult,
                      derived: &StoreInferredFactResult| {
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
            ("store", project_store(&derived.store, runtime)),
        ]);
        result.push(object_for(runtime, fields));
    };
    for atomic in atomic {
        match atomic {
            InferAtomicFactResult::LessFact(rules) => {
                for rule in rules {
                    let InferLessFactResult::StrictLowerBoundPositive(p) = rule;
                    append(
                        "StrictLowerBoundPositive",
                        p.source_fact_id,
                        None,
                        &p.bound_nonnegative_proof,
                        &p.derived,
                    );
                }
            }
            InferAtomicFactResult::GreaterFact(rules) => {
                for rule in rules {
                    let InferGreaterFactResult::StrictLowerBoundPositive(p) = rule;
                    append(
                        "StrictLowerBoundPositive",
                        p.source_fact_id,
                        None,
                        &p.bound_nonnegative_proof,
                        &p.derived,
                    );
                }
            }
            InferAtomicFactResult::LessEqualFact(rules) => {
                for rule in rules {
                    let InferLessEqualFactResult::WeakIntegerLowerBoundInN(p) = rule;
                    append(
                        "WeakIntegerLowerBoundInN",
                        p.source_fact_id,
                        Some(&p.integer_proof),
                        &p.bound_nonnegative_proof,
                        &p.derived,
                    );
                }
            }
            InferAtomicFactResult::GreaterEqualFact(rules) => {
                for rule in rules {
                    let InferGreaterEqualFactResult::WeakIntegerLowerBoundInN(p) = rule;
                    append(
                        "WeakIntegerLowerBoundInN",
                        p.source_fact_id,
                        Some(&p.integer_proof),
                        &p.bound_nonnegative_proof,
                        &p.derived,
                    );
                }
            }
            _ => {}
        }
    }
    result
}

fn project_prop_definition_infer(infer: &InferResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic = match infer {
        InferResult::AtomicFact(atomic) => vec![atomic],
        InferResult::AndFact(and) => and.components.iter().collect(),
        InferResult::ChainFact(chain) => chain
            .adjacent_infers
            .iter()
            .map(|edge| &edge.infer)
            .collect(),
        InferResult::OrFact(_)
        | InferResult::ExistFact(_)
        | InferResult::ExistUniqueFact(_)
        | InferResult::NotExistFact(_)
        | InferResult::NotForall(_)
        | InferResult::ForallFact(_)
        | InferResult::ForallFactWithIff(_) => return Vec::new(),
    };
    let mut rules = Vec::new();
    for atomic in atomic {
        let InferAtomicFactResult::NormalAtomicFact(infer) = atomic else {
            continue;
        };
        for rule in infer {
            let (name, derived) = match rule {
                InferNormalAtomicFactResult::ParamTypes(result) => {
                    ("NormalAtomicParamTypes", &result.derived)
                }
                InferNormalAtomicFactResult::ExpandDefinition(result) => {
                    ("NormalAtomicExpandDefinition", &result.derived)
                }
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
                                        vec![("store", project_store(&result.store, runtime))],
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

fn project_signed_standard_set_infer(infer: &InferResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic = match infer {
        InferResult::AtomicFact(atomic) => vec![atomic],
        InferResult::AndFact(and) => and.components.iter().collect(),
        InferResult::ChainFact(chain) => chain
            .adjacent_infers
            .iter()
            .map(|edge| &edge.infer)
            .collect(),
        InferResult::OrFact(_)
        | InferResult::ExistFact(_)
        | InferResult::ExistUniqueFact(_)
        | InferResult::NotExistFact(_)
        | InferResult::NotForall(_)
        | InferResult::ForallFact(_)
        | InferResult::ForallFactWithIff(_) => return Vec::new(),
    };
    let mut rules = Vec::new();
    for atomic in atomic {
        let InferAtomicFactResult::InFact(infer) = atomic else {
            continue;
        };
        for rule in infer {
            let InferInFactResult::SignedStandardSetSign(proof) = rule else {
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
                                        vec![("store", project_store(&captured.store, runtime))],
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

fn project_cancellation_infer(infer: &InferResult, runtime: &Runtime) -> Vec<JsonValue> {
    let mut rules = Vec::new();
    match infer {
        InferResult::AtomicFact(atomic) => {
            rules.extend(project_cancellation_atomic(atomic, runtime))
        }
        InferResult::AndFact(and) => {
            for atomic in &and.components {
                rules.extend(project_cancellation_atomic(atomic, runtime));
            }
        }
        InferResult::ChainFact(chain) => {
            for atomic in &chain.adjacent_infers {
                rules.extend(project_cancellation_atomic(&atomic.infer, runtime));
            }
        }
        InferResult::OrFact(_)
        | InferResult::ExistFact(_)
        | InferResult::ExistUniqueFact(_)
        | InferResult::NotExistFact(_)
        | InferResult::NotForall(_)
        | InferResult::ForallFact(_)
        | InferResult::ForallFactWithIff(_) => {}
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
            InferEqualFactResult::AdditiveCancellation(r) => rules.push(object_for(
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
                            vec![("store", project_store(&r.derived.store, runtime))],
                        ),
                    ),
                ],
            )),
            InferEqualFactResult::NonzeroFactorCancellation(r) => rules.push(object_for(
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
            InferEqualFactResult::SubtractiveCancellation(r) => rules.push(object_for(
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
            InferEqualFactResult::CommonDenominatorCancellation(r) => rules.push(object_for(
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
            InferEqualFactResult::NonzeroNumeratorCancellation(r) => rules.push(object_for(
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
            InferEqualFactResult::PositiveRealPower(_) => {}
        }
    }
    rules
}

fn project_positive_power_infer(infer: &InferResult, runtime: &Runtime) -> Vec<JsonValue> {
    let atomic: Vec<&InferAtomicFactResult> = match infer {
        InferResult::AtomicFact(atomic) => vec![atomic],
        InferResult::AndFact(and) => and.components.iter().collect(),
        InferResult::ChainFact(chain) => chain
            .adjacent_infers
            .iter()
            .map(|edge| &edge.infer)
            .collect(),
        _ => Vec::new(),
    };
    atomic.into_iter().flat_map(|atomic| {
        let InferAtomicFactResult::EqualFact(rules) = atomic else { return Vec::new(); };
        rules.iter().filter_map(|rule| {
            let InferEqualFactResult::PositiveRealPower(rule) = rule else { return None; };
            Some(object_for(runtime, vec![
                ("rule", string("PositiveRealPower")),
                ("transports", JsonValue::Array(rule.transports.iter().map(|transport| {
                    let (variant, proof) = match &transport.positivity {
                        InferPositiveRealPowerPositivityResult::PowerPositive(proof) => ("PowerPositive", proof),
                        InferPositiveRealPowerPositivityResult::BasePositive(proof) => ("BasePositive", proof),
                    };
                    object_for(runtime, vec![
                        ("source", fact_id_entry(runtime, transport.source_fact_id)),
                        ("power", string(transport.power.readable_string())),
                        ("positivity", object_for(runtime, vec![
                            ("type", string(variant)),
                            ("proof", super::verify::project_verify_fact(proof, runtime)),
                        ])),
                        ("exponent_real", super::verify::project_verify_fact(&transport.exponent_real, runtime)),
                        ("derived", project_inferred_store(&transport.derived, runtime)),
                    ])
                }).collect())),
            ]))
        }).collect::<Vec<_>>()
    }).collect()
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
        vec![("store", project_store(&result.store, runtime))],
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

pub(super) fn project_signature_selection(
    selected: &crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection;
    let mut fields = vec![(
        "signature",
        string(
            Obj::FunctionSpace(FunctionSpace::FnSet(selected.signature().clone()))
                .readable_string(),
        ),
    )];
    match selected {
        FunctionSignatureSelection::AnonymousLiteral { .. } => {
            fields.push(("source", string("anonymous_literal")))
        }
        FunctionSignatureSelection::Property { fact_id, .. } => {
            fields.push(("source", fact_id_entry(runtime, *fact_id)))
        }
        FunctionSignatureSelection::DeclaredField { .. } => {
            fields.push(("source", string("declared_field")))
        }
    }
    object_for(runtime, fields)
}
