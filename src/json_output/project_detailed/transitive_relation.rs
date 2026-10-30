use crate::prelude::*;
use super::super::helper::{object_for, string};
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_transitive_relation::TransitiveRelationProof;

pub(super) fn project_transitive_relation(
    proof: &TransitiveRelationProof,
    runtime: &Runtime,
) -> JsonValue {
    let mut fields = vec![
        (
            "known_left_fact_id",
            string(proof.known_left_fact_id.to_string()),
        ),
        (
            "residual_fact",
            string(proof.residual_fact.readable_string()),
        ),
        (
            "proof_of_residual_fact",
            project_verify_fact(&proof.proof_of_residual_fact, runtime),
        ),
    ];
    if let Some(fact) = runtime.fact_by_id_in_stack(proof.known_left_fact_id) {
        fields.push(("known_left_fact", string(fact.readable_string())));
    }
    object_for(runtime, fields)
}
