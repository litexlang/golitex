use crate::execute::execute_eval_stmt::aggregate_evaluation_result::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_aggregate_evaluations(
    proofs: &[AggregateEvaluationResult],
    runtime: &Runtime,
) -> JsonValue {
    JsonValue::Array(
        proofs
            .iter()
            .map(|p| {
                let (kind, source, domain, terms, value) = match p {
                    AggregateEvaluationResult::Sum(p) => (
                        "sum",
                        &p.source,
                        project_bounds(&p.bounds, runtime),
                        &p.terms,
                        &p.value,
                    ),
                    AggregateEvaluationResult::SumOfFiniteSet(p) => (
                        "finite_set_sum",
                        &p.source,
                        project_enumeration(&p.enumeration, runtime),
                        &p.terms,
                        &p.value,
                    ),
                    AggregateEvaluationResult::Product(p) => (
                        "product",
                        &p.source,
                        project_bounds(&p.bounds, runtime),
                        &p.terms,
                        &p.value,
                    ),
                    AggregateEvaluationResult::ProductOfFiniteSet(p) => (
                        "finite_set_product",
                        &p.source,
                        project_enumeration(&p.enumeration, runtime),
                        &p.terms,
                        &p.value,
                    ),
                };
                object_for(
                    runtime,
                    vec![
                        ("kind", string(kind)),
                        ("source", string(source.readable_string())),
                        ("enumeration", domain),
                        (
                            "terms",
                            JsonValue::Array(
                                terms.iter().map(|p| project_term(p, runtime)).collect(),
                            ),
                        ),
                        ("value", string(value.readable_string())),
                    ],
                )
            })
            .collect(),
    )
}

fn project_bounds(p: &AggregateRangeBoundsResult, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("start", string(p.start.readable_string())),
            ("end", string(p.end.readable_string())),
            ("cited_equal_fact_ids", cites(&p.cited_equal_fact_ids)),
        ],
    )
}
fn project_enumeration(p: &FiniteSetEnumerationResult, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "set_equality",
                super::searched::project_known_equality_path(&p.set_equality, runtime),
            ),
            ("resolved_set", string(p.resolved_set.readable_string())),
            ("cited_equal_fact_ids", cites(&p.cited_equal_fact_ids)),
            (
                "elements",
                JsonValue::Array(
                    p.elements
                        .iter()
                        .map(|o| string(o.readable_string()))
                        .collect(),
                ),
            ),
        ],
    )
}
fn project_term(p: &AggregateTermEvaluationResult, runtime: &Runtime) -> JsonValue {
    let expansion = match &p.expansion {
        AggregateTermExpansion::Function(p) => object_for(
            runtime,
            vec![
                (
                    "function_equal",
                    super::searched::project_known_equality_path(&p.function_equal, runtime),
                ),
                ("expanded_body", string(p.expanded_body.readable_string())),
            ],
        ),
        AggregateTermExpansion::Algorithm { evaluation_index } => {
            string(format!("algo_evaluation[{evaluation_index}]"))
        }
    };
    object_for(
        runtime,
        vec![
            ("argument", string(p.argument.readable_string())),
            ("application", string(p.application.readable_string())),
            (
                "application_well_defined",
                super::wd::project_obj_wd_proof(&p.application_well_defined, runtime),
            ),
            ("expansion", expansion),
            (
                "nested_aggregate_evidence",
                string(format!(
                    "{}..{}",
                    p.nested_aggregate_evidence.start, p.nested_aggregate_evidence.end
                )),
            ),
            ("value", string(p.value.readable_string())),
            (
                "accumulated_value",
                string(p.accumulated_value.readable_string()),
            ),
        ],
    )
}
pub(super) fn project_function_evaluations(
    proofs: &[FunctionApplicationEvaluationResult],
    runtime: &Runtime,
) -> JsonValue {
    JsonValue::Array(
        proofs
            .iter()
            .map(|p| {
                object_for(
                    runtime,
                    vec![
                        ("application", string(p.application.readable_string())),
                        (
                            "application_well_defined",
                            super::wd::project_obj_wd_proof(&p.application_well_defined, runtime),
                        ),
                        (
                            "function_equal",
                            super::searched::project_known_equality_path(
                                &p.expansion.function_equal,
                                runtime,
                            ),
                        ),
                        (
                            "expanded_body",
                            string(p.expansion.expanded_body.readable_string()),
                        ),
                        ("value", string(p.value.readable_string())),
                    ],
                )
            })
            .collect(),
    )
}
pub(super) fn cites(ids: &[crate::runtime::FactId]) -> JsonValue {
    JsonValue::Array(ids.iter().map(|id| string(id.to_string())).collect())
}

pub(super) fn project_algo_evaluations(
    proofs: &[AlgoApplicationEvaluationResult],
    runtime: &Runtime,
) -> JsonValue {
    JsonValue::Array(
        proofs
            .iter()
            .map(|p| {
                object_for(
                    runtime,
                    vec![
                        ("application", string(p.application.readable_string())),
                        (
                            "normalized_arguments",
                            JsonValue::Array(
                                p.normalized_arguments
                                    .iter()
                                    .map(|a| string(a.readable_string()))
                                    .collect(),
                            ),
                        ),
                        (
                            "return_expression",
                            string(p.return_expression.readable_string()),
                        ),
                        (
                            "definition_evidence",
                            match &p.definition_evidence {
                                AlgoDefinitionEvidence::Display => string("display"),
                                AlgoDefinitionEvidence::Checked(proof) => {
                                    super::verify::project_verify_fact(proof, runtime)
                                }
                            },
                        ),
                        ("value", string(p.value.readable_string())),
                    ],
                )
            })
            .collect(),
    )
}
