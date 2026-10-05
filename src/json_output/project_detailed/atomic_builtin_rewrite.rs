//! Project the checked atomic rewrite, including its original child evidence.

use super::store::project_verify_facts;
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_atomic_builtin_rewrite(
    proof: &AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
    runtime: &Runtime,
) -> JsonValue {
    let (rule, rewritten_fact, cited_equal_fact_ids, proof_of_rewritten_fact) = match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(p) => (
            "ClosedNumericEqualSubstitution",
            &p.rewritten_fact,
            &p.cited_equal_fact_ids,
            &p.proof_of_rewritten_fact,
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(p) => (
            "KnownEqualObjSubstitution",
            &p.rewritten_fact,
            &p.cited_equal_fact_ids,
            &p.proof_of_rewritten_fact,
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(p) => {
            return object_for(runtime, vec![
                ("type", string("by_builtin_rewrite")),
                ("rule", string("FnApplicationUnfoldSubstitution")),
                ("rewritten_fact", string(p.rewritten_fact.readable_string())),
                ("unfold_equal_proofs", project_verify_facts(&p.unfold_equal_proofs, runtime)),
                ("proof_of_rewritten_fact", project_verify_fact(&p.proof_of_rewritten_fact, runtime)),
            ]);
        }
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(p) => {
            return object_for(runtime, vec![
                ("type", string("by_builtin_rewrite")),
                ("rule", string("OrderDual")),
                ("alternate_fact", string(p.alternate_fact.readable_string())),
                ("proof_of_alternate_fact", project_verify_fact(&p.proof_of_alternate_fact, runtime)),
            ]);
        }
    };
    let cites = cited_equal_fact_ids.iter().map(|id| {
        let mut fields = vec![("fact_id", string(id.to_string()))];
        if let Some(fact) = runtime.fact_by_id_in_stack(*id) {
            fields.push(("fact", string(fact.readable_string())));
        }
        object_for(runtime, fields)
    }).collect();
    object_for(runtime, vec![
        ("type", string("by_builtin_rewrite")),
        ("rule", string(rule)),
        ("rewritten_fact", string(rewritten_fact.readable_string())),
        ("cited_equal_fact_ids", JsonValue::Array(cites)),
        ("proof_of_rewritten_fact", project_verify_fact(proof_of_rewritten_fact, runtime)),
    ])
}
