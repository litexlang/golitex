use super::searched::project_equal_searched;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,
    InFactSearchProofByKnownSpecialProperty,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_known_special_property(
    proof: &AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,
    runtime: &Runtime,
) -> JsonValue {
    let (rule, id, matches) = match proof {
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(p),
        ) => (
            "FnApplicationInCodomain",
            p.cite_property_fact_id,
            p.signature_return_matches
                .iter()
                .map(|p| {
                    object_for(
                        runtime,
                        vec![
                            (
                                "cite_signature_fact_id",
                                string(p.cite_signature_fact_id.to_string()),
                            ),
                            (
                                "return_set_match",
                                project_equal_searched(&p.return_set_match, runtime),
                            ),
                        ],
                    )
                })
                .collect(),
        ),
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(p),
        ) => (
            "FnApplicationInFnRange",
            p.cite_property_fact_id,
            p.signature_matches
                .iter()
                .map(|p| {
                    object_for(
                        runtime,
                        vec![
                            (
                                "cite_signature_fact_id",
                                string(p.cite_signature_fact_id.to_string()),
                            ),
                            (
                                "signature_match",
                                project_equal_searched(&p.signature_match, runtime),
                            ),
                        ],
                    )
                })
                .collect(),
        ),
    };
    let mut fields = vec![
        ("type", string("by_known_special_property")),
        ("family", string("InFact")),
        ("rule", string(rule)),
        ("cite_property_fact_id", string(id.to_string())),
        ("signature_matches", JsonValue::Array(matches)),
    ];
    if let Some(fact) = runtime.fact_by_id_in_stack(id) {
        fields.push(("cite", string(fact.readable_string())));
    }
    object_for(runtime, fields)
}
