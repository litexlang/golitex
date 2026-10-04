//! Checked beta steps and their selected mathematical function bodies.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::normalize_function_body::{FunctionBodyNormalizationProof, FunctionBodySourceProof};
use crate::ast::obj::{Obj, FunctionSpace};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
use super::searched::project_known_equality_path;
use super::wd::project_obj_wd_proof;

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
                        .map(|step| {
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
                                } => object_for(
                                    runtime,
                                    vec![
                                        ("type", string("template")),
                                        ("instance", string(instance.readable_string())),
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
