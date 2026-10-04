//! Preserve the source paths and signature evidence of known tuple elimination.
use crate::ast::fact::AtomicFact;
use crate::ast::obj::{Obj, ProductShape};
use crate::execute::execute_fact_stmt::known_tuple::{
    KnownFunctionTupleApplicability, KnownFunctionTupleValueProof, KnownTemplateSignatureMatchProof, KnownTupleShapeProof, KnownTupleValueProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_known_special_property::EqualFactSearchProofByKnownSpecialProperty;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
use super::searched::{project_equal_searched, project_known_equality_path};

pub(super) fn project_equal_known_tuple(
    proof: &EqualFactSearchProofByKnownSpecialProperty,
    runtime: &Runtime,
) -> JsonValue {
    let mut fields = vec![("type", string("by_known_special_property"))];
    match proof {
        EqualFactSearchProofByKnownSpecialProperty::TupleReconstruction(p) => {
            fields.extend([
                ("rule", string("TupleReconstruction")),
                ("reversed", JsonValue::Bool(p.reversed)),
                ("shape", project_shape(&p.shape, runtime)),
                (
                    "subjects",
                    JsonValue::Array(
                        p.subjects
                            .iter()
                            .map(|p| project_equal_searched(p, runtime))
                            .collect(),
                    ),
                ),
            ]);
        }
        EqualFactSearchProofByKnownSpecialProperty::TupleProjection(p) => {
            fields.extend([
                ("rule", string("TupleProjection")),
                ("reversed", JsonValue::Bool(p.reversed)),
                ("index", string(p.index.to_string())),
                ("tuple", project_value(&p.tuple, runtime)),
                (
                    "component_equal",
                    project_equal_searched(&p.component_equal, runtime),
                ),
            ]);
        }
        EqualFactSearchProofByKnownSpecialProperty::FnTupleProjection(p) => {
            let applicability = project_function_applicability(&p.function, runtime);
            fields.extend([
                ("rule", string("FnTupleProjection")),
                ("reversed", JsonValue::Bool(p.reversed)),
                ("index", string(p.index.to_string())),
                ("subject_equal", project_known_equality_path(&p.subject_equal, runtime)),
                (
                    "function_equal",
                    project_known_equality_path(&p.function.function_equal, runtime),
                ),
                ("applicability", applicability),
                (
                    "expanded_body",
                    string(
                        Obj::ProductShape(ProductShape::Tuple(p.function.value.clone()))
                            .readable_string(),
                    ),
                ),
                (
                    "component_equal",
                    project_equal_searched(&p.component_equal, runtime),
                ),
            ]);
        }
        EqualFactSearchProofByKnownSpecialProperty::FnTupleValue(p) => {
            fields.extend([
                ("rule", string("FnTupleValue")),
                ("reversed", JsonValue::Bool(p.reversed)),
                ("subject_equal", project_known_equality_path(&p.subject_equal, runtime)),
                ("function_equal", project_known_equality_path(&p.function.function_equal, runtime)),
                ("applicability", project_function_applicability(&p.function, runtime)),
                ("expanded_body", string(Obj::ProductShape(ProductShape::Tuple(p.function.value.clone())).readable_string())),
                ("value_equal", project_equal_searched(&p.value_equal, runtime)),
            ]);
        }
        EqualFactSearchProofByKnownSpecialProperty::TupleDimension(p) => {
            fields.extend([
                ("rule", string("TupleDimension")),
                ("reversed", JsonValue::Bool(p.reversed)),
                ("shape", project_shape(&p.shape, runtime)),
                (
                    "dimension_equal",
                    project_equal_searched(&p.dimension_equal, runtime),
                ),
            ]);
        }
    }
    object_for(runtime, fields)
}

pub(super) fn project_atomic_tuple_shape(
    rule: &str,
    shape: &KnownTupleShapeProof,
    index: Option<usize>,
    runtime: &Runtime,
) -> JsonValue {
    let mut fields = vec![
        ("type", string("by_known_special_property")),
        ("rule", string(rule)),
        ("shape", project_shape(shape, runtime)),
    ];
    if let Some(index) = index {
        fields.push(("index", string(index.to_string())));
    }
    object_for(runtime, fields)
}

pub(super) fn project_shape(shape: &KnownTupleShapeProof, runtime: &Runtime) -> JsonValue {
    let mut fields = vec![("dimension", string(shape.dimension().to_string()))];
    match shape {
        KnownTupleShapeProof::CartesianMembership(p) => {
            fields.extend([
                ("kind", string("cartesian_membership")),
                (
                    "subject_equal",
                    project_known_equality_path(&p.subject_equal, runtime),
                ),
                ("cite_fact_id", string(p.membership.fact_id.to_string())),
                (
                    "membership",
                    string(AtomicFact::InFact(p.membership.clone()).readable_string()),
                ),
                (
                    "carrier_equal",
                    project_known_equality_path(&p.carrier_equal, runtime),
                ),
            ]);
        }
        KnownTupleShapeProof::TupleEquality(p) => {
            fields.extend([
                ("kind", string("tuple_equality")),
                ("tuple", project_value(p, runtime)),
            ]);
        }
        KnownTupleShapeProof::FunctionCodomain(p) => {
            fields.extend([
                ("kind", string("function_codomain")),
                (
                    "function_equal",
                    project_known_equality_path(&p.function_equal, runtime),
                ),
                (
                    "membership",
                    string(AtomicFact::InFact(p.membership.clone()).readable_string()),
                ),
                (
                    "cite_property_fact_id",
                    string(p.membership_proof.cite_property_fact_id.to_string()),
                ),
                (
                    "signature_matches",
                    JsonValue::Array(
                        p.membership_proof
                            .signature_return_matches
                            .iter()
                            .map(|m| {
                                object_for(
                                    runtime,
                                    vec![
                                        (
                                            "cite_signature_fact_id",
                                            string(m.cite_signature_fact_id.to_string()),
                                        ),
                                        (
                                            "return_set_match",
                                            project_equal_searched(&m.return_set_match, runtime),
                                        ),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                ),
                (
                    "carrier_equal",
                    project_known_equality_path(&p.carrier_equal, runtime),
                ),
            ]);
        }
    }
    object_for(runtime, fields)
}

fn project_value(value: &KnownTupleValueProof, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "tuple_equal",
                project_known_equality_path(&value.tuple_equal, runtime),
            ),
            (
                "value",
                string(
                    Obj::ProductShape(ProductShape::Tuple(value.value.clone())).readable_string(),
                ),
            ),
        ],
    )
}

fn project_function_applicability(proof: &KnownFunctionTupleValueProof, runtime: &Runtime) -> JsonValue {
    match &proof.applicability {
        KnownFunctionTupleApplicability::AnonymousLiteral => object_for(runtime, vec![("kind", string("anonymous_literal"))]),
        KnownFunctionTupleApplicability::AllSignaturesMatch { signatures, template_signatures } => object_for(runtime, vec![
            ("kind", string("all_signatures_match")),
            ("matches", project_signature_matches(signatures, runtime)),
            ("template_matches", project_template_signature_matches(template_signatures, runtime)),
        ]),
        KnownFunctionTupleApplicability::TemplateDefinition { instance, signature, alternative_signatures, alternative_template_signatures } => object_for(runtime, vec![
            ("kind", string("template_definition")),
            ("instance", string(Obj::InstantiatedTemplateObj(instance.clone()).readable_string())),
            ("signature", string(Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(signature.clone())).readable_string())),
            ("matches", project_signature_matches(alternative_signatures, runtime)),
            ("template_matches", project_template_signature_matches(alternative_template_signatures, runtime)),
        ]),
    }
}

fn project_signature_matches(matches: &[crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::SignatureMatchProof], runtime: &Runtime) -> JsonValue {
    JsonValue::Array(matches.iter().map(|p| object_for(runtime, vec![
        ("cite_signature_fact_id", string(p.cite_signature_fact_id.to_string())),
        ("signature_match", project_equal_searched(&p.signature_match, runtime)),
    ])).collect())
}

fn project_template_signature_matches(matches: &[KnownTemplateSignatureMatchProof], runtime: &Runtime) -> JsonValue {
    JsonValue::Array(matches.iter().map(|p| object_for(runtime, vec![
        ("function_equal", project_known_equality_path(&p.function_equal, runtime)),
        ("instance", string(Obj::InstantiatedTemplateObj(p.instance.clone()).readable_string())),
        ("signature_match", project_equal_searched(&p.signature_match, runtime)),
    ])).collect())
}
