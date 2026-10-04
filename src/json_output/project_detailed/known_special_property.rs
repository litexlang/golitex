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
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(p)) => return object_for(runtime, vec![
            ("type", string("by_known_special_property")),
            ("rule", string("FnApplicationInStandardSuperset")),
            ("target_set", string(crate::ast::obj::Obj::StandardSet(p.target_set.clone()).readable_string())),
            ("signature_returns", JsonValue::Array(p.signature_returns.iter().map(|s| object_for(runtime, vec![
                ("cite_signature_fact_id", string(s.cite_signature_fact_id.to_string())),
                ("source_set", string(crate::ast::obj::Obj::StandardSet(s.source_set.clone()).readable_string())),
                ("function_equal", super::searched::project_known_equality_path(&s.function_equal, runtime)),
            ])).collect())),
        ]),
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(InFactSearchProofByKnownSpecialProperty::StandardNumericSuperset(p)) => return object_for(runtime, vec![
            ("type", string("by_known_special_property")),
            ("rule", string("StandardNumericSuperset")),
            ("source_set", string(crate::ast::obj::Obj::StandardSet(p.source_set.clone()).readable_string())),
            ("target_set", string(crate::ast::obj::Obj::StandardSet(p.target_set.clone()).readable_string())),
            ("source_membership_proof", super::searched::project_known_premise(&p.source_membership_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(InFactSearchProofByKnownSpecialProperty::FoldInCarrier(p)) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::FoldOperationSignatureProof;
            let signature=match &p.operation_signature {
                FoldOperationSignatureProof::Literal(signature)=>object_for(runtime,vec![("type",string("literal_signature")),("signature",string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(signature.clone())).readable_string()))]),
                FoldOperationSignatureProof::Known(p)=>super::searched::project_known_premise(p,runtime),
            };
            return object_for(runtime,vec![("type",string("by_known_special_property")),("rule",string("FoldInCarrier")),("operation_signature",signature),("carrier",string(p.carrier.readable_string())),("carrier_match",project_equal_searched(&p.carrier_match,runtime))]);
        },
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(InFactSearchProofByKnownSpecialProperty::AnonymousFnApplicationInCodomain(p)) => return object_for(runtime,vec![
            ("type",string("by_known_special_property")),("rule",string("AnonymousFnApplicationInCodomain")),
            ("signature",string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(p.signature.clone())).readable_string())),
            ("applied_return_set",string(p.applied_return_set.readable_string())),("return_set_match",project_equal_searched(&p.return_set_match,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(InFactSearchProofByKnownSpecialProperty::FieldApplicationInDeclaredCodomain(p)) => return object_for(runtime, vec![
            ("type", string("by_known_special_property")),
            ("rule", string("FieldApplicationInDeclaredCodomain")),
            ("declared_signature", string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(p.declared_signature.clone())).readable_string())),
            ("applied_return_set", string(p.applied_return_set.readable_string())),
            ("return_set_match", project_equal_searched(&p.return_set_match, runtime)),
            ("alternative_signature_matches", JsonValue::Array(p.alternative_signature_matches.iter().map(|candidate| object_for(runtime, vec![
                ("cite_signature_fact_id", string(candidate.cite_signature_fact_id.to_string())),
                ("return_set_match", project_equal_searched(&candidate.return_set_match, runtime)),
            ])).collect())),
        ]),
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(InFactSearchProofByKnownSpecialProperty::TemplateApplicationInDeclaredCodomain(p)) => return object_for(runtime, vec![
            ("type", string("by_known_special_property")),
            ("rule", string("TemplateApplicationInDeclaredCodomain")),
            ("instance", string(crate::ast::obj::Obj::InstantiatedTemplateObj(p.instance.clone()).readable_string())),
            ("function_equal", super::searched::project_known_equality_path(&p.function_equal, runtime)),
            ("declared_signature", string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(p.declared_signature.clone())).readable_string())),
            ("applied_return_set", string(p.applied_return_set.readable_string())),
            ("return_set_match", project_equal_searched(&p.return_set_match, runtime)),
            ("alternative_signature_matches", JsonValue::Array(p.alternative_signature_matches.iter().map(|candidate| object_for(runtime, vec![
                ("cite_signature_fact_id", string(candidate.cite_signature_fact_id.to_string())),
                ("return_set_match", project_equal_searched(&candidate.return_set_match, runtime)),
            ])).collect())),
            ("alternative_template_signature_matches", JsonValue::Array(p.alternative_template_signature_matches.iter().map(|candidate| object_for(runtime, vec![
                ("instance", string(crate::ast::obj::Obj::InstantiatedTemplateObj(candidate.instance.clone()).readable_string())),
                ("function_equal", super::searched::project_known_equality_path(&candidate.function_equal, runtime)),
                ("return_set_match", project_equal_searched(&candidate.return_set_match, runtime)),
            ])).collect())),
        ]),
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(InFactSearchProofByKnownSpecialProperty::FieldInDeclaredSet(p)) => return object_for(runtime, vec![
            ("type", string("by_known_special_property")),
            ("rule", string("FieldInDeclaredSet")),
            ("declared_set", string(p.declared_set.readable_string())),
            ("set_match", project_equal_searched(&p.set_match, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::IsTuple(p) => {
            return super::known_tuple::project_atomic_tuple_shape("IsTuple", &p.shape, None, runtime);
        }
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::TupleIndexUpperBound(p) => {
            return object_for(runtime, vec![
                ("type", string("by_known_special_property")),
                ("rule", string("TupleIndexUpperBound")),
                ("shape", super::known_tuple::project_shape(&p.shape, runtime)),
                ("source_bound", super::searched::project_known_premise(&p.source_bound, runtime)),
            ]);
        }
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::TupleIndexBound(p) => {
            return super::known_tuple::project_atomic_tuple_shape("TupleIndexBound", &p.shape, Some(p.index), runtime);
        }
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::HomogeneousTupleCoordinate(p),
        ) => {
            return object_for(runtime, vec![
                ("type", string("by_known_special_property")),
                ("rule", string("HomogeneousTupleCoordinate")),
                ("shape", super::known_tuple::project_shape(&p.shape, runtime)),
                ("carrier_equals", JsonValue::Array(p.carrier_equals.iter()
                    .map(|p| project_equal_searched(p, runtime)).collect())),
            ]);
        }
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::TupleCoordinate(p),
        ) => {
            return object_for(runtime, vec![
                ("type", string("by_known_special_property")),
                ("rule", string("TupleCoordinate")),
                ("index", string(p.index.to_string())),
                ("shape", super::known_tuple::project_shape(&p.shape, runtime)),
                ("carrier_equal", project_equal_searched(&p.carrier_equal, runtime)),
            ]);
        }
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
