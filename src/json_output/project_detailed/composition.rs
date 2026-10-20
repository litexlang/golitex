//! Projection of constructor, cached interface, and failed compatibility evidence.
use super::function_domain::project_source;
use super::searched::project_known_equality_path;
use super::wd::{project_obj_wd_proof, project_verify_obj_wd};
use crate::prelude::*;

pub(super) fn construction(proof: &CompositionObjWellDefinedProof, rt: &Runtime) -> JsonValue {
    crate::json_output::helper::object_for(
        rt,
        vec![
            ("type", crate::json_output::helper::string("by_def")),
            (
                "family",
                crate::json_output::helper::string("FunctionSpace"),
            ),
            ("kind", crate::json_output::helper::string("Composition")),
            (
                "obj",
                crate::json_output::helper::string(
                    Obj::from(Composition::new(
                        proof.outer_well_defined.obj().clone(),
                        proof.inner_well_defined.obj().clone(),
                    ))
                    .readable_string(),
                ),
            ),
            (
                "outer_well_defined",
                project_obj_wd_proof(&proof.outer_well_defined, rt),
            ),
            (
                "inner_well_defined",
                project_obj_wd_proof(&proof.inner_well_defined, rt),
            ),
            ("outer_domain", project_source(&proof.outer_domain, rt)),
            ("inner_domain", project_source(&proof.inner_domain, rt)),
            (
                "function",
                crate::json_output::helper::string(
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(proof.function.clone()))
                        .readable_string(),
                ),
            ),
            (
                "function_well_defined",
                project_obj_wd_proof(&proof.function_well_defined, rt),
            ),
        ],
    )
}

pub(super) fn callable(proof: &CompositionCallableProof, rt: &Runtime) -> JsonValue {
    let signature = match &proof.signature {
        CompositionSignatureProof::Construction => {
            crate::json_output::helper::string("checked_construction")
        }
        CompositionSignatureProof::Interfaces {
            outer_domain,
            inner_domain,
        } => crate::json_output::helper::object_for(
            rt,
            vec![
                (
                    "type",
                    crate::json_output::helper::string("derived_composition_interfaces"),
                ),
                ("outer_domain", project_source(outer_domain, rt)),
                ("inner_domain", project_source(inner_domain, rt)),
            ],
        ),
    };
    crate::json_output::helper::object_for(
        rt,
        vec![
            (
                "type",
                crate::json_output::helper::string("checked_composition"),
            ),
            (
                "composition",
                crate::json_output::helper::string(
                    Obj::from(proof.composition.clone()).readable_string(),
                ),
            ),
            (
                "function_equal",
                project_known_equality_path(&proof.function_equal, rt),
            ),
            (
                "well_defined",
                match &proof.well_defined {
                    CompositionWellDefinedPremise::Checked(wd) => project_obj_wd_proof(wd, rt),
                    CompositionWellDefinedPremise::ParentAtomic => {
                        crate::json_output::helper::string("parent_atomic_well_defined")
                    }
                },
            ),
            ("signature_source", signature),
            (
                "function",
                crate::json_output::helper::string(
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(proof.function.clone()))
                        .readable_string(),
                ),
            ),
        ],
    )
}

pub(super) fn failure(reason: &CompositionFailure, rt: &Runtime) -> JsonValue {
    match reason {
        CompositionFailure::Operand(failed) => project_verify_obj_wd(failed, rt),
        CompositionFailure::NoUnaryOuterDomain => crate::json_output::helper::string("compose: outer function needs a checked complete unary interface"),
        CompositionFailure::NoInnerDomain => crate::json_output::helper::string("compose: inner function needs a checked complete interface"),
        CompositionFailure::Compatibility(attempts) => crate::json_output::helper::object_for(rt, vec![
            ("type", crate::json_output::helper::string("unproved_composition_compatibility")),
            ("message", crate::json_output::helper::string("compose: outer call must be well-defined for every input in the complete inner domain")),
            ("attempts", JsonValue::Array(attempts.iter().map(|p| project_verify_obj_wd(p, rt)).collect())),
        ]),
    }
}

pub(super) fn equality(
    proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_composition::CompositionEqualityProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_composition::CompositionEqualityProof as P;
    let mut fields = vec![
        ("type", crate::json_output::helper::string("builtin_rule")),
        ("rule", crate::json_output::helper::string(proof.rule_id())),
    ];
    match proof {
        P::Associativity(p) => {
            fields.push((
                "left",
                crate::json_output::helper::string(Obj::from(p.left.clone()).readable_string()),
            ));
            fields.push((
                "right",
                crate::json_output::helper::string(Obj::from(p.right.clone()).readable_string()),
            ));
        }
        P::LeftIdentity(p) => {
            fields.push((
                "identity",
                crate::json_output::helper::string(
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.identity.clone()))
                        .readable_string(),
                ),
            ));
            fields.push((
                "identity_equal",
                project_known_equality_path(&p.identity_equal, rt),
            ));
        }
        P::RightIdentity(p) => {
            fields.push((
                "identity",
                crate::json_output::helper::string(
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.identity.clone()))
                        .readable_string(),
                ),
            ));
            fields.push((
                "identity_equal",
                project_known_equality_path(&p.identity_equal, rt),
            ));
            fields.push((
                "full_domain",
                super::function_domain::project_function_domain(&p.full_domain, rt),
            ));
        }
        P::Definition(p) => {
            fields.push(("callable", callable(&p.callable, rt)));
            fields.push((
                "function",
                crate::json_output::helper::string(
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.function.clone()))
                        .readable_string(),
                ),
            ));
            fields.push((
                "function_equal",
                project_known_equality_path(&p.function_equal, rt),
            ));
        }
    }
    crate::json_output::helper::object_for(rt, fields)
}
