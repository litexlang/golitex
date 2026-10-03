//! Evidence for ordered-fold leaf rules, including scoped translations.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::reduce_rule_helper::{ReduceNonemptyProof, ReduceObjectMatchMethod, ReduceObjectMatchProof};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_pointwise_certificate(
    p: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_pointwise::ReducePointwiseCertificate,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("by_known_forall_fact")),
            (
                "fact",
                string(crate::ast::fact::Fact::ForallFact(p.fact.clone()).readable_string()),
            ),
            ("cite_fact_id", string(p.cite_fact_id.to_string())),
            (
                "parameter_renamings",
                JsonValue::Array(
                    p.parameter_renamings
                        .iter()
                        .map(|r| {
                            object_for(
                                rt,
                                vec![
                                    ("source", string(r.source.to_string())),
                                    ("target", string(r.target.to_string())),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
        ],
    )
}

pub(super) fn project_matches(proofs: &[ReduceObjectMatchProof], rt: &Runtime) -> JsonValue {
    JsonValue::Array(proofs.iter().map(|p| project_match(p, rt)).collect())
}
pub(super) fn project_match(p: &ReduceObjectMatchProof, rt: &Runtime) -> JsonValue {
    let method = match &p.method {
        ReduceObjectMatchMethod::SameIr => object_for(rt, vec![("type", string("SameIr"))]),
        ReduceObjectMatchMethod::RationalNormalization => {
            object_for(rt, vec![("type", string("RationalNormalization"))])
        }
        ReduceObjectMatchMethod::KnownEquality(proof) => {
            super::searched::project_equal_searched(proof, rt)
        }
        ReduceObjectMatchMethod::ApplicationArguments(args) => object_for(
            rt,
            vec![
                ("type", string("ApplicationArguments")),
                ("arguments", project_matches(args, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("left", string(p.left.readable_string())),
            ("right", string(p.right.readable_string())),
            ("method", method),
        ],
    )
}
pub(super) fn project_nonempty(p: &ReduceNonemptyProof, rt: &Runtime) -> JsonValue {
    match p {
        ReduceNonemptyProof::Known(proof) => super::verify::project_verify_fact(proof, rt),
        ReduceNonemptyProof::ClosedIntegerComparison { start, end } => object_for(
            rt,
            vec![
                ("type", string("ClosedIntegerComparison")),
                ("start", string(start.readable_string())),
                ("end", string(end.readable_string())),
            ],
        ),
    }
}
