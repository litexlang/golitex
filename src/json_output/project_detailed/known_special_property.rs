use super::searched::project_equal_searched;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,
    InFactSearchProofByKnownSpecialProperty,
    SignatureCodomainUseProof,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_known_special_property(
    proof: &AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(p) => {
            project_in_fact_special(p, runtime)
        }
    }
}
pub(super) fn project_in_fact_special(
    proof: &InFactSearchProofByKnownSpecialProperty,
    runtime: &Runtime,
) -> JsonValue {
    let (rule, id, matches) = match proof {
        InFactSearchProofByKnownSpecialProperty::DeclaredNumericSequenceCarrier(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("DeclaredNumericSequenceCarrier")),
                    (
                        "declared_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.declared_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "target_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.target_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "widened_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.widened_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "source_return",
                        string(
                            crate::ast::obj::Obj::StandardSet(p.source_return.clone())
                                .readable_string(),
                        ),
                    ),
                    (
                        "target_return",
                        string(
                            crate::ast::obj::Obj::StandardSet(p.target_return.clone())
                                .readable_string(),
                        ),
                    ),
                    (
                        "signature_match",
                        project_equal_searched(&p.signature_match, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::RealMatrixApplicationCodomain(p) => {
            return project_real_array_application(p, runtime)
        }
        InFactSearchProofByKnownSpecialProperty::UniformTupleCoordinateCarrier(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("UniformTupleCoordinateCarrier")),
                    (
                        "tuple_equal",
                        super::searched::project_known_equality_path(&p.tuple.tuple_equal, runtime),
                    ),
                    ("index", string(p.index.readable_string())),
                    (
                        "coordinates",
                        JsonValue::Array(
                            p.coordinates
                                .iter()
                                .map(|p| {
                                    super::structural_membership::project_structural_membership(
                                        p, runtime,
                                    )
                                })
                                .collect(),
                        ),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::KnownFunctionInExactCarrier(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("KnownFunctionInExactCarrier")),
                    (
                        "membership",
                        super::searched::project_known_premise(&p.membership, runtime),
                    ),
                    (
                        "signature_match",
                        project_equal_searched(&p.signature_match, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::DeclaredFunctionInExactCarrier(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("DeclaredFunctionInExactCarrier")),
                    (
                        "normalized_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(
                                    p.normalized_signature.clone(),
                                ),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "target_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.target_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "subject_equal",
                        super::searched::project_known_equality_path(&p.subject_equal, runtime),
                    ),
                    (
                        "signature_match",
                        project_equal_searched(&p.signature_match, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::MultivariableSelectorInCarrier(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("MultivariableSelectorInCarrier")),
                    (
                        "declared_carrier",
                        string(p.declared_carrier.readable_string()),
                    ),
                    (
                        "carrier_match",
                        project_equal_searched(&p.carrier_match, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::MultivariableSelectorApplicationInCodomain(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("MultivariableSelectorApplicationInCodomain")),
                    (
                        "applied_return_set",
                        string(p.applied_return_set.readable_string()),
                    ),
                    (
                        "return_set_match",
                        project_equal_searched(&p.return_set_match, runtime),
                    ),
                ],
            )
        }

        InFactSearchProofByKnownSpecialProperty::FiniteTupleInStandardFunctionSpace(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("FiniteTupleInStandardFunctionSpace")),
                    (
                        "tuple_equal",
                        super::searched::project_known_equality_path(
                            &p.source.tuple_equal,
                            runtime,
                        ),
                    ),
                    (
                        "signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "coordinates",
                        JsonValue::Array(
                            p.coordinates
                                .iter()
                                .map(|p| {
                                    super::structural_membership::project_structural_membership(
                                        p, runtime,
                                    )
                                })
                                .collect(),
                        ),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::LiteralTupleNumericCoordinate(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("LiteralTupleNumericCoordinate")),
                    ("index", string(p.index.to_string())),
                    (
                        "tuple_equal",
                        super::searched::project_known_equality_path(&p.tuple.tuple_equal, runtime),
                    ),
                    (
                        "value",
                        string(
                            crate::ast::obj::Obj::ProductShape(
                                crate::ast::obj::ProductShape::Tuple(p.tuple.value.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "component_membership",
                        super::closed_calculation::project_membership(
                            "in",
                            &p.component_membership,
                            runtime,
                        ),
                    ),
                ],
            );
        }
        InFactSearchProofByKnownSpecialProperty::KnownSubsetMembership(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("KnownSubsetMembership")),
                    (
                        "member_proof",
                        super::searched::project_known_premise(&p.member_proof, runtime),
                    ),
                    (
                        "subset_proof",
                        super::searched::project_known_premise(&p.subset_proof, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::PositiveRealFromKnownStrictOrder(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("PositiveRealFromKnownStrictOrder")),
                    (
                        "positive_order",
                        super::searched::project_known_premise(&p.positive_order, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::AnonymousFnInFiniteSeq(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("AnonymousFnInFiniteSeq")),
                    (
                        "declared_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.declared_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "signature_match",
                        project_equal_searched(&p.signature_match, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::TemplateFunctionInDeclaredFnSet(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("TemplateFunctionInDeclaredFnSet")),
                    (
                        "instance",
                        string(
                            crate::ast::obj::Obj::InstantiatedTemplateObj(p.instance.clone())
                                .readable_string(),
                        ),
                    ),
                    (
                        "declared_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.declared_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "signature_match",
                        project_equal_searched(&p.signature_match, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::FnApplicationInStandardSuperset(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("FnApplicationInStandardSuperset")),
                    (
                        "target_set",
                        string(
                            crate::ast::obj::Obj::StandardSet(p.target_set.clone())
                                .readable_string(),
                        ),
                    ),
                    (
                        "signature_returns",
                        JsonValue::Array(
                            p.signature_returns
                                .iter()
                                .map(|s| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "cite_signature_fact_id",
                                                string(s.cite_signature_fact_id.to_string()),
                                            ),
                                            (
                                                "source_set",
                                                string(
                                                    crate::ast::obj::Obj::StandardSet(
                                                        s.source_set.clone(),
                                                    )
                                                    .readable_string(),
                                                ),
                                            ),
                                            (
                                                "function_equal",
                                                super::searched::project_known_equality_path(
                                                    &s.function_equal,
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
            )
        }
        InFactSearchProofByKnownSpecialProperty::StandardNumericSuperset(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("StandardNumericSuperset")),
                    (
                        "source_set",
                        string(
                            crate::ast::obj::Obj::StandardSet(p.source_set.clone())
                                .readable_string(),
                        ),
                    ),
                    (
                        "target_set",
                        string(
                            crate::ast::obj::Obj::StandardSet(p.target_set.clone())
                                .readable_string(),
                        ),
                    ),
                    (
                        "source_membership_proof",
                        super::searched::project_known_premise(&p.source_membership_proof, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::FoldInCarrier(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::FoldOperationSignatureProof;
            let signature = match &p.operation_signature {
                FoldOperationSignatureProof::Literal(signature) => object_for(
                    runtime,
                    vec![
                        ("type", string("literal_signature")),
                        (
                            "signature",
                            string(
                                crate::ast::obj::Obj::FunctionSpace(
                                    crate::ast::obj::FunctionSpace::FnSet(signature.clone()),
                                )
                                .readable_string(),
                            ),
                        ),
                    ],
                ),
                FoldOperationSignatureProof::Known(p) => {
                    super::searched::project_known_premise(p, runtime)
                }
            };
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("FoldInCarrier")),
                    ("operation_signature", signature),
                    ("carrier", string(p.carrier.readable_string())),
                    (
                        "carrier_match",
                        project_equal_searched(&p.carrier_match, runtime),
                    ),
                ],
            );
        }
        InFactSearchProofByKnownSpecialProperty::AnonymousFnApplicationInCodomain(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("AnonymousFnApplicationInCodomain")),
                    (
                        "signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "applied_return_set",
                        string(p.applied_return_set.readable_string()),
                    ),
                    (
                        "return_set_match",
                        project_equal_searched(&p.return_set_match, runtime),
                    ),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::FieldApplicationInDeclaredCodomain(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("FieldApplicationInDeclaredCodomain")),
                    (
                        "declared_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.declared_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "applied_return_set",
                        string(p.applied_return_set.readable_string()),
                    ),
                    (
                        "return_set_match",
                        project_equal_searched(&p.return_set_match, runtime),
                    ),
                    (
                        "alternative_signature_matches",
                        JsonValue::Array(
                            p.alternative_signature_matches
                                .iter()
                                .map(|candidate| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "cite_signature_fact_id",
                                                string(
                                                    candidate.cite_signature_fact_id.to_string(),
                                                ),
                                            ),
                                            (
                                                "return_set_match",
                                                project_equal_searched(
                                                    &candidate.return_set_match,
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
            )
        }
        InFactSearchProofByKnownSpecialProperty::TemplateApplicationInDeclaredCodomain(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("TemplateApplicationInDeclaredCodomain")),
                    (
                        "instance",
                        string(
                            crate::ast::obj::Obj::InstantiatedTemplateObj(p.instance.clone())
                                .readable_string(),
                        ),
                    ),
                    (
                        "function_equal",
                        super::searched::project_known_equality_path(&p.function_equal, runtime),
                    ),
                    (
                        "declared_signature",
                        string(
                            crate::ast::obj::Obj::FunctionSpace(
                                crate::ast::obj::FunctionSpace::FnSet(p.declared_signature.clone()),
                            )
                            .readable_string(),
                        ),
                    ),
                    (
                        "applied_return_set",
                        string(p.applied_return_set.readable_string()),
                    ),
                    (
                        "return_set_match",
                        project_equal_searched(&p.return_set_match, runtime),
                    ),
                    (
                        "alternative_signature_matches",
                        JsonValue::Array(
                            p.alternative_signature_matches
                                .iter()
                                .map(|candidate| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "cite_signature_fact_id",
                                                string(
                                                    candidate.cite_signature_fact_id.to_string(),
                                                ),
                                            ),
                                            (
                                                "return_set_match",
                                                project_equal_searched(
                                                    &candidate.return_set_match,
                                                    runtime,
                                                ),
                                            ),
                                        ],
                                    )
                                })
                                .collect(),
                        ),
                    ),
                    (
                        "alternative_template_signature_matches",
                        JsonValue::Array(
                            p.alternative_template_signature_matches
                                .iter()
                                .map(|candidate| {
                                    object_for(
                                        runtime,
                                        vec![
                                            (
                                                "instance",
                                                string(
                                                    crate::ast::obj::Obj::InstantiatedTemplateObj(
                                                        candidate.instance.clone(),
                                                    )
                                                    .readable_string(),
                                                ),
                                            ),
                                            (
                                                "function_equal",
                                                super::searched::project_known_equality_path(
                                                    &candidate.function_equal,
                                                    runtime,
                                                ),
                                            ),
                                            (
                                                "return_set_match",
                                                project_equal_searched(
                                                    &candidate.return_set_match,
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
            )
        }
        InFactSearchProofByKnownSpecialProperty::FieldInDeclaredSet(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("FieldInDeclaredSet")),
                    ("declared_set", string(p.declared_set.readable_string())),
                    ("set_match", project_equal_searched(&p.set_match, runtime)),
                ],
            )
        }
        InFactSearchProofByKnownSpecialProperty::HomogeneousTupleCoordinate(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("HomogeneousTupleCoordinate")),
                    (
                        "shape",
                        super::known_tuple::project_shape(&p.shape, runtime),
                    ),
                    (
                        "carrier_equals",
                        JsonValue::Array(
                            p.carrier_equals
                                .iter()
                                .map(|p| project_equal_searched(p, runtime))
                                .collect(),
                        ),
                    ),
                ],
            );
        }
        InFactSearchProofByKnownSpecialProperty::TupleCoordinate(p) => {
            return object_for(
                runtime,
                vec![
                    ("type", string("by_known_special_property")),
                    ("rule", string("TupleCoordinate")),
                    ("index", string(p.index.to_string())),
                    (
                        "shape",
                        super::known_tuple::project_shape(&p.shape, runtime),
                    ),
                    (
                        "carrier_equal",
                        project_equal_searched(&p.carrier_equal, runtime),
                    ),
                ],
            );
        }
        InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(p) => (
            "FnApplicationInCodomain",
            p.cite_property_fact_id,
            p.signature_uses
                .iter()
                .map(|p| project_signature_codomain_use(p, runtime))
                .collect(),
        ),
        InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(p) => (
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
    if let InFactSearchProofByKnownSpecialProperty::FnApplicationInCodomain(proof) = proof {
        fields.push((
            "function_equal",
            super::searched::project_known_equality_path(&proof.function_equal, runtime),
        ));
    }
    if let InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(proof) = proof {
        fields.push((
            "function_equal",
            super::searched::project_known_equality_path(&proof.function_equal, runtime),
        ));
    }
    object_for(runtime, fields)
}

pub(super) fn project_signature_codomain_use(
    proof: &SignatureCodomainUseProof,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        SignatureCodomainUseProof::ReturnSetMatch(proof) => object_for(
            runtime,
            vec![
                ("type", string("return_set_match")),
                (
                    "cite_signature_fact_id",
                    string(proof.cite_signature_fact_id.to_string()),
                ),
                (
                    "return_set_match",
                    project_equal_searched(&proof.return_set_match, runtime),
                ),
            ],
        ),
        SignatureCodomainUseProof::SameCallDomains {
            cite_signature_fact_id,
            function_equal,
            domains,
        } => object_for(
            runtime,
            vec![
                ("type", string("same_call_domains")),
                (
                    "cite_signature_fact_id",
                    string(cite_signature_fact_id.to_string()),
                ),
                (
                    "function_equal",
                    super::searched::project_known_equality_path(function_equal, runtime),
                ),
                (
                    "domain_comparison",
                    super::function_domain::project_call_domains_alpha_match(domains, runtime),
                ),
            ],
        ),
    }
}

fn project_real_array_application(
    p:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::RealMatrixApplicationCodomainProof,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("by_known_special_property")),
            ("rule", string("RealMatrixApplicationCodomain")),
            ("array", project_real_array(&p.array, rt)),
            ("applied_return", string(p.applied_return.readable_string())),
        ],
    )
}
fn project_real_array(
    p:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::RealNativeArrayCarrierProof,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            (
                "operator",
                string(crate::ast::obj::Obj::MatrixOperator(p.operator.clone()).readable_string()),
            ),
            (
                "signature",
                string(
                    crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(
                        p.signature.clone(),
                    ))
                    .readable_string(),
                ),
            ),
            (
                "real_operands",
                JsonValue::Array(
                    p.real_operands
                        .iter()
                        .map(|p| project_real_operand(p, rt))
                        .collect(),
                ),
            ),
        ],
    )
}
fn project_real_operand(
    p:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::DeclaredRealOperandProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::known_real_array_return::DeclaredRealOperandSource;
    let source = match &p.source {
        DeclaredRealOperandSource::Known(p) => super::searched::project_known_premise(p, rt),
        DeclaredRealOperandSource::Structural(p) => {
            super::structural_membership::project_structural_membership(p, rt)
        }
        DeclaredRealOperandSource::Special(p) => project_in_fact_special(p, rt),
        DeclaredRealOperandSource::NativeArray(p) => project_real_array(p, rt),
        DeclaredRealOperandSource::NativeApplication(p) => project_real_array_application(p, rt),
        DeclaredRealOperandSource::RealArithmetic(p) => object_for(
            rt,
            vec![
                ("rule", string("RealArithmetic")),
                ("expression", string(p.expression.readable_string())),
                (
                    "operands",
                    JsonValue::Array(
                        p.operands
                            .iter()
                            .map(|p| project_real_operand(p, rt))
                            .collect(),
                    ),
                ),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            (
                "requirement",
                string(
                    crate::ast::fact::AtomicFact::InFact(p.requirement.clone()).readable_string(),
                ),
            ),
            ("proof", source),
        ],
    )
}
