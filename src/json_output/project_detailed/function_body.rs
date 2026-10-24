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
    let mut fields = vec![
        ("type", string("by_object_definition")),
        ("kind", string("fn_application_parent_checked_beta")),
    ];
    match proof {
        ByParentCheckedBetaObjectDefinitionProof::OneSide(p) => {
            fields.extend([
                (
                    "parent_well_defined_side",
                    string(match p.parent_well_defined_side {
                        ParentEqualitySide::Left => "left",
                        ParentEqualitySide::Right => "right",
                    }),
                ),
                (
                    "function_body",
                    project_parent_checked_function_body(&p.function_body, runtime),
                ),
                ("expanded_body", string(p.expanded_body.readable_string())),
                (
                    "residual_equal",
                    string(
                        crate::ast::fact::Fact::from(p.residual_equal.clone()).readable_string(),
                    ),
                ),
                (
                    "residual_proof",
                    super::searched::project_equal_searched(&p.residual_proof, runtime),
                ),
            ]);
        }
        ByParentCheckedBetaObjectDefinitionProof::TwoSides(p) => {
            fields.extend([
                ("parent_well_defined_side", string("both")),
                (
                    "left_function_body",
                    project_parent_checked_function_body(&p.left_function_body, runtime),
                ),
                (
                    "left_expanded_body",
                    string(p.left_expanded_body.readable_string()),
                ),
                (
                    "right_function_body",
                    project_parent_checked_function_body(&p.right_function_body, runtime),
                ),
                (
                    "right_expanded_body",
                    string(p.right_expanded_body.readable_string()),
                ),
                (
                    "residual_equal",
                    string(
                        crate::ast::fact::Fact::from(p.residual_equal.clone()).readable_string(),
                    ),
                ),
                (
                    "residual_proof",
                    super::searched::project_equal_searched(&p.residual_proof, runtime),
                ),
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
        ParentCheckedBetaFunctionBody::NativeMatrix(proof) => {
            super::native_matrix::callable(proof, runtime)
        }
        ParentCheckedBetaFunctionBody::StructField(proof) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::struct_field_value::StructTupleValueSource;
            let source = match &proof.source {
                StructTupleValueSource::Known(p) => super::known_tuple::project_value(p, runtime),
                StructTupleValueSource::Function(p) => object_for(
                    runtime,
                    vec![
                        ("type", string("function_tuple")),
                        (
                            "function_equal",
                            project_known_equality_path(&p.function_equal, runtime),
                        ),
                        (
                            "applicability",
                            super::known_tuple::project_function_applicability(p, runtime),
                        ),
                        (
                            "value",
                            string(
                                Obj::ProductShape(crate::ast::obj::ProductShape::Tuple(
                                    p.value.clone(),
                                ))
                                .readable_string(),
                            ),
                        ),
                    ],
                ),
                StructTupleValueSource::ReturnedFunction {
                    body,
                    application_well_defined,
                    function,
                } => object_for(
                    runtime,
                    vec![
                        ("type", string("returned_function_tuple")),
                        ("body", project_parent_checked_function_body(body, runtime)),
                        (
                            "application_well_defined",
                            super::wd::project_obj_wd_proof(application_well_defined, runtime),
                        ),
                        (
                            "function_equal",
                            project_known_equality_path(&function.function_equal, runtime),
                        ),
                        (
                            "applicability",
                            super::known_tuple::project_function_applicability(function, runtime),
                        ),
                        (
                            "value",
                            string(
                                Obj::ProductShape(crate::ast::obj::ProductShape::Tuple(
                                    function.value.clone(),
                                ))
                                .readable_string(),
                            ),
                        ),
                    ],
                ),
                StructTupleValueSource::Template { instance, value } => object_for(
                    runtime,
                    vec![
                        ("type", string("template_tuple")),
                        (
                            "instance",
                            string(
                                Obj::InstantiatedTemplateObj(instance.clone()).readable_string(),
                            ),
                        ),
                        (
                            "value",
                            string(
                                Obj::ProductShape(crate::ast::obj::ProductShape::Tuple(
                                    value.clone(),
                                ))
                                .readable_string(),
                            ),
                        ),
                    ],
                ),
                StructTupleValueSource::Returned { body, value } => object_for(
                    runtime,
                    vec![
                        ("type", string("returned_tuple")),
                        ("body", project_parent_checked_function_body(body, runtime)),
                        (
                            "value",
                            string(
                                Obj::ProductShape(crate::ast::obj::ProductShape::Tuple(
                                    value.clone(),
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
                    ("type", string("struct_field_value")),
                    (
                        "receiver_well_defined",
                        super::wd::project_obj_wd_proof(&proof.receiver_well_defined, runtime),
                    ),
                    (
                        "carrier",
                        string(
                            Obj::StructAndFieldAccessObj(
                                crate::ast::obj::StructAndFieldAccessObj::StructObj(
                                    proof.carrier.clone(),
                                ),
                            )
                            .readable_string(),
                        ),
                    ),
                    ("index", string(proof.index.to_string())),
                    ("source", source),
                ],
            )
        }
        ParentCheckedBetaFunctionBody::KnownFiniteFunctionCoordinate { source, index } => {
            object_for(
                runtime,
                vec![
                    ("type", string("finite_function_coordinate")),
                    (
                        "source",
                        super::function_domain::project_finite_function_source(source, runtime),
                    ),
                    ("index", string(index.to_string())),
                ],
            )
        }
        ParentCheckedBetaFunctionBody::ReturnedFiniteFunctionCoordinate {
            receiver_well_defined,
            receiver_function_body,
            returned_tuple,
            index,
        } => object_for(
            runtime,
            vec![
                ("type", string("returned_finite_function_coordinate")),
                (
                    "application_well_defined",
                    super::wd::project_obj_wd_proof(receiver_well_defined, runtime),
                ),
                (
                    "function_body",
                    project_parent_checked_function_body(receiver_function_body, runtime),
                ),
                (
                    "value",
                    string(
                        Obj::ProductShape(crate::ast::obj::ProductShape::Tuple(
                            returned_tuple.clone(),
                        ))
                        .readable_string(),
                    ),
                ),
                ("index", string(index.to_string())),
            ],
        ),
        ParentCheckedBetaFunctionBody::ReturnedAnonymousFunctionApplication {
            receiver_well_defined,
            receiver_function_body,
            returned_function,
        } => object_for(
            runtime,
            vec![
                ("type", string("returned_anonymous_function_application")),
                (
                    "application_well_defined",
                    super::wd::project_obj_wd_proof(receiver_well_defined, runtime),
                ),
                (
                    "function_body",
                    project_parent_checked_function_body(receiver_function_body, runtime),
                ),
                (
                    "function",
                    string(
                        Obj::FunctionSpace(crate::ast::obj::FunctionSpace::AnonymousFn(
                            returned_function.clone(),
                        ))
                        .readable_string(),
                    ),
                ),
            ],
        ),
        ParentCheckedBetaFunctionBody::ReturnedKnownFunctionApplication {
            receiver_well_defined,
            receiver_function_body,
            application_well_defined,
            application_function_body,
        } => object_for(
            runtime,
            vec![
                ("type", string("returned_known_function_application")),
                (
                    "receiver_well_defined",
                    super::wd::project_obj_wd_proof(receiver_well_defined, runtime),
                ),
                (
                    "receiver_function_body",
                    project_parent_checked_function_body(receiver_function_body, runtime),
                ),
                (
                    "application_well_defined",
                    super::wd::project_obj_wd_proof(application_well_defined, runtime),
                ),
                (
                    "application_function_body",
                    project_parent_checked_function_body(application_function_body, runtime),
                ),
            ],
        ),
        ParentCheckedBetaFunctionBody::TemplateAnonymousFunction {
            template_instance,
            function,
            domain,
        } => object_for(
            runtime,
            vec![
                ("type", string("template_anonymous_function")),
                (
                    "template_instance",
                    string(template_instance.readable_string()),
                ),
                (
                    "function",
                    string(
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()))
                            .readable_string(),
                    ),
                ),
                (
                    "domain",
                    project_template_application_domain(domain, runtime),
                ),
            ],
        ),
        ParentCheckedBetaFunctionBody::Composition {
            composition,
            function_equal,
        } => object_for(
            runtime,
            vec![
                ("type", string("composition_application")),
                (
                    "composition",
                    string(Obj::from(composition.clone()).readable_string()),
                ),
                (
                    "function_equal",
                    project_known_equality_path(function_equal, runtime),
                ),
            ],
        ),
        ParentCheckedBetaFunctionBody::AnonymousLiteral => {
            object_for(runtime, vec![("type", string("anonymous_literal"))])
        }
        ParentCheckedBetaFunctionBody::KnownAnonymousFunction {
            function,
            function_equal,
            checked_domain,
        } => object_for(
            runtime,
            vec![
                ("type", string("known_anonymous_function")),
                (
                    "function",
                    string(
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()))
                            .readable_string(),
                    ),
                ),
                (
                    "function_equal",
                    project_known_equality_path(function_equal, runtime),
                ),
                (
                    "checked_domain",
                    string(
                        Obj::FunctionSpace(FunctionSpace::FnSet(checked_domain.clone()))
                            .readable_string(),
                    ),
                ),
            ],
        ),
    }
}

fn project_template_application_domain(
    domain: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::TemplateApplicationDomainProof,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::TemplateApplicationDomainProof;
    let (checked, kind) = match domain {
        TemplateApplicationDomainProof::Parent { checked_domain } => (checked_domain, "parent"),
        TemplateApplicationDomainProof::Rechecked { checked_domain, .. } => {
            (checked_domain, "rechecked")
        }
    };
    let mut fields = vec![
        ("type", string(kind)),
        (
            "checked_domain",
            string(Obj::FunctionSpace(FunctionSpace::FnSet(checked.clone())).readable_string()),
        ),
    ];
    if let TemplateApplicationDomainProof::Rechecked {
        argument_well_defined,
        requirement_fact_verified,
        argument_scope,
        ..
    } = domain
    {
        fields.push((
            "argument_scope",
            argument_scope
                .as_ref()
                .map(|scope| super::wd_by_def::project_fn_argument_scope(scope, runtime))
                .unwrap_or(JsonValue::Null),
        ));
        fields.push((
            "argument_well_defined",
            JsonValue::Array(
                argument_well_defined
                    .iter()
                    .map(|proof| super::wd::project_obj_wd_proof(proof, runtime))
                    .collect(),
            ),
        ));
        fields.push((
            "requirement_fact_verified",
            JsonValue::Array(
                requirement_fact_verified
                    .iter()
                    .map(|proof| super::verify::project_verify_fact(proof, runtime))
                    .collect(),
            ),
        ));
    }
    object_for(runtime, fields)
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
                            FunctionBodyExpansionProof::Composition(step) => object_for(
                                runtime,
                                vec![
                                    ("type", string("composition_beta")),
                                    ("application", string(step.application.readable_string())),
                                    (
                                        "application_well_defined",
                                        project_obj_wd_proof(
                                            &step.application_well_defined,
                                            runtime,
                                        ),
                                    ),
                                    (
                                        "function_equal",
                                        project_known_equality_path(&step.function_equal, runtime),
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
                            ),
                            FunctionBodyExpansionProof::FiniteCoordinate(step) => object_for(
                                runtime,
                                vec![
                                    ("type", string("finite_function_coordinate")),
                                    ("application", string(step.application.readable_string())),
                                    (
                                        "application_well_defined",
                                        project_obj_wd_proof(
                                            &step.application_well_defined,
                                            runtime,
                                        ),
                                    ),
                                    (
                                        "source",
                                        super::function_domain::project_finite_function_source(
                                            &step.source,
                                            runtime,
                                        ),
                                    ),
                                    ("index", string(step.index.to_string())),
                                    (
                                        "expanded_body",
                                        string(step.expanded_body.readable_string()),
                                    ),
                                    (
                                        "continued_body",
                                        string(step.continued_body.readable_string()),
                                    ),
                                ],
                            ),
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
                                            (
                                                "function_equal",
                                                project_known_equality_path(
                                                    function_equal,
                                                    runtime,
                                                ),
                                            ),
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
