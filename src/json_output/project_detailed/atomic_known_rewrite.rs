use super::super::helper::{object_for, string};
use crate::prelude::*;

pub(super) fn project_atomic_known_rewrite(
    proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByKnownRewrite,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByKnownRewrite as Rule;
    let mut fields = vec![("type", string("by_known_rewrite"))];
    match proof {
        Rule::Reflexivity(proof) => {
            fields.push(("rule", string("Reflexivity")));
            fields.push(("cite_prop", string(proof.cite_prop.to_string())));
        }
        Rule::Symmetry(proof) => {
            fields.push(("rule", string("Symmetry")));
            fields.push(("cite_prop", string(proof.cite_prop.to_string())));
            fields.push((
                "argument_permutation",
                JsonValue::Array(
                    proof
                        .argument_permutation
                        .iter()
                        .map(|n| string(n.to_string()))
                        .collect(),
                ),
            ));
            fields.push((
                "alternate_fact",
                string(proof.alternate_fact.readable_string()),
            ));
            fields.push((
                "proof_of_alternate_fact",
                super::verify::project_verify_fact(&proof.proof_of_alternate_fact, runtime),
            ));
        }
        Rule::Transitivity(proof) => {
            fields.push(("rule", string("Transitivity")));
            fields.push(("cite_prop", string(proof.cite_prop.to_string())));
            fields.push((
                "application",
                super::transitive_relation::project_transitive_relation(
                    &proof.application,
                    runtime,
                ),
            ));
        }
    }
    object_for(runtime, fields)
}
