//! Checked beta steps and their selected mathematical function bodies.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{FunctionBodyExpansionProof, FunctionBodyNormalizationProof, FunctionBodySourceProof};
use crate::ast::obj::{Obj, FunctionSpace};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
use super::searched::project_known_equality_path;
use super::wd::project_obj_wd_proof;

pub(super) fn project_parent_checked_beta(
    proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::ByParentCheckedBetaObjectDefinitionProof,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentEqualitySide};
    let mut fields = vec![("type", string("by_object_definition")), ("kind", string("fn_application_parent_checked_beta"))];
    match proof {
        ByParentCheckedBetaObjectDefinitionProof::OneSide(p) => {
            fields.extend([
                ("parent_well_defined_side", string(match p.parent_well_defined_side { ParentEqualitySide::Left => "left", ParentEqualitySide::Right => "right" })),
                ("function_body", project_parent_checked_function_body(&p.function_body, runtime)),
                ("expanded_body", string(p.expanded_body.readable_string())),
                ("residual_equal", string(crate::ast::fact::Fact::from(p.residual_equal.clone()).readable_string())),
                ("residual_proof", super::searched::project_equal_searched(&p.residual_proof, runtime)),
            ]);
        }
        ByParentCheckedBetaObjectDefinitionProof::TwoSides(p) => {
            fields.extend([
                ("parent_well_defined_side", string("both")),
                ("left_function_body", project_parent_checked_function_body(&p.left_function_body, runtime)),
                ("left_expanded_body", string(p.left_expanded_body.readable_string())),
                ("right_function_body", project_parent_checked_function_body(&p.right_function_body, runtime)),
                ("right_expanded_body", string(p.right_expanded_body.readable_string())),
                ("residual_equal", string(crate::ast::fact::Fact::from(p.residual_equal.clone()).readable_string())),
                ("residual_proof", super::searched::project_equal_searched(&p.residual_proof, runtime)),
            ]);
        }
    }
    object_for(runtime, fields)
}

pub(super) fn project_parent_checked_function_body(
    proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::ParentCheckedBetaFunctionBody,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::ParentCheckedBetaFunctionBody;
    match proof {
        ParentCheckedBetaFunctionBody::KnownFiniteFunctionCoordinate { source, index } => object_for(runtime, vec![
            ("type", string("finite_function_coordinate")),
            ("source", super::function_domain::project_finite_function_source(source, runtime)),
            ("index", string(index.to_string())),
        ]),
        ParentCheckedBetaFunctionBody::ReturnedFiniteFunctionCoordinate { receiver_well_defined, receiver_function_body, returned_tuple, index } => object_for(runtime, vec![
            ("type", string("returned_finite_function_coordinate")),
            ("application_well_defined", super::wd::project_obj_wd_proof(receiver_well_defined, runtime)),
            ("function_body", project_parent_checked_function_body(receiver_function_body, runtime)),
            ("value", string(Obj::ProductShape(crate::ast::obj::ProductShape::Tuple(returned_tuple.clone())).readable_string())),
            ("index", string(index.to_string())),
        ]),
        ParentCheckedBetaFunctionBody::ReturnedAnonymousFunctionApplication { receiver_well_defined, receiver_function_body, returned_function } => object_for(runtime, vec![
            ("type", string("returned_anonymous_function_application")),
            ("application_well_defined", super::wd::project_obj_wd_proof(receiver_well_defined, runtime)),
            ("function_body", project_parent_checked_function_body(receiver_function_body, runtime)),
            ("function", string(Obj::FunctionSpace(crate::ast::obj::FunctionSpace::AnonymousFn(returned_function.clone())).readable_string())),
        ]),
        ParentCheckedBetaFunctionBody::AnonymousLiteral => object_for(runtime, vec![("type", string("anonymous_literal"))]),
        ParentCheckedBetaFunctionBody::KnownAnonymousFunction { function, function_equal, checked_domain } => object_for(runtime, vec![
            ("type", string("known_anonymous_function")),
            ("function", string(Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone())).readable_string())),
            ("function_equal", project_known_equality_path(function_equal, runtime)),
            ("checked_domain", string(Obj::FunctionSpace(FunctionSpace::FnSet(checked_domain.clone())).readable_string())),
        ]),
    }
}

pub(super) fn project_function_body_normalization(
    proof: &FunctionBodyNormalizationProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            (
                "expansions",
                JsonValue::Array(
                    proof
                        .expansions
                        .iter()
                        .map(|step| match step {
                            FunctionBodyExpansionProof::FiniteCoordinate(step) => object_for(runtime, vec![
                                ("type", string("finite_function_coordinate")),
                                ("application", string(step.application.readable_string())),
                                ("application_well_defined", project_obj_wd_proof(&step.application_well_defined, runtime)),
                                ("source", super::function_domain::project_finite_function_source(&step.source, runtime)),
                                ("index", string(step.index.to_string())),
                                ("expanded_body", string(step.expanded_body.readable_string())),
                                ("continued_body", string(step.continued_body.readable_string())),
                            ]),
                            FunctionBodyExpansionProof::Anonymous(step) => {
                            let function_body = match &step.function_body {
                                FunctionBodySourceProof::KnownEquality(path) => object_for(
                                    runtime,
                                    vec![
                                        ("type", string("known_equality")),
                                        (
                                            "function_equal",
                                            project_known_equality_path(path, runtime),
                                        ),
                                    ],
                                ),
                                FunctionBodySourceProof::Template {
                                    instance,
                                    instantiated_function,
                                    function_equal,
                                } => object_for(
                                    runtime,
                                    vec![
                                        ("type", string("template")),
                                        ("instance", string(instance.readable_string())),
                                        ("function_equal", project_known_equality_path(function_equal, runtime)),
                                        (
                                            "instantiated_function",
                                            string(
                                                Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                                                    instantiated_function.clone(),
                                                ))
                                                .readable_string(),
                                            ),
                                        ),
                                    ],
                                ),
                            };
                            object_for(
                                runtime,
                                vec![
                                    ("application", string(step.application.readable_string())),
                                    (
                                        "application_well_defined",
                                        project_obj_wd_proof(
                                            &step.application_well_defined,
                                            runtime,
                                        ),
                                    ),
                                    ("function_body", function_body),
                                    (
                                        "body_application_well_defined",
                                        project_obj_wd_proof(
                                            &step.body_application_well_defined,
                                            runtime,
                                        ),
                                    ),
                                    (
                                        "expanded_body",
                                        string(step.expanded_body.readable_string()),
                                    ),
                                    (
                                        "continued_body",
                                        string(step.continued_body.readable_string()),
                                    ),
                                ],
                            )
                            }
                        })
                        .collect(),
                ),
            ),
            (
                "expanded_body",
                string(proof.expanded_body.readable_string()),
            ),
        ],
    )
}
