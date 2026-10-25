use crate::execute::execute_fact_stmt::multivariable::selector::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn object_wd(p: &MultivariableSelectorWellDefinedStages, rt: &Runtime) -> JsonValue {
    let selection = match &p.selection {
        MultivariableSelectorSelectionProof::Candidate(c) => {
            super::searched::project_known_premise(c, rt)
        }
        MultivariableSelectorSelectionProof::Existence { fact, proof } => object_for(
            rt,
            vec![
                ("existence", string(fact.readable_string())),
                ("proof", super::verify::project_verify_fact(proof, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("kind", string("multivariable_selector")),
            (
                "arguments",
                JsonValue::Array(
                    p.argument_well_defined
                        .iter()
                        .map(|a| super::wd::project_obj_wd_proof(a, rt))
                        .collect(),
                ),
            ),
            (
                "function_domain",
                super::function_domain::project_source(&p.function_domain, rt),
            ),
            ("domains", requirements(&p.domains, rt)),
            ("selection", selection),
        ],
    )
}
pub(super) fn requirements(
    p:&[crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainWellDefinedProof],
    rt: &Runtime,
) -> JsonValue {
    JsonValue::Array(
        p.iter()
            .map(|p| {
                object_for(
                    rt,
                    vec![
                        ("requirement", string(p.requirement.readable_string())),
                        ("proof", super::verify::project_verify_fact(&p.result, rt)),
                    ],
                )
            })
            .collect(),
    )
}
pub(super) fn object_failure(stage: &MultivariableSelectorFailureStage, rt: &Runtime) -> JsonValue {
    match stage {
        MultivariableSelectorFailureStage::Argument(p)=>object_for(rt,vec![("stage",string("argument")),("failure",super::wd_failure::project_obj_wd_failure(p,rt))]),
        MultivariableSelectorFailureStage::FunctionDomain=>object_for(rt,vec![("stage",string("function_domain")),("message",string("Requires a complete real Euclidean function with the declared dimensions."))]),
        MultivariableSelectorFailureStage::Domain {requirement,proof}=>object_for(rt,vec![("stage",string("domain")),("requirement",string(requirement.readable_string())),("proof",super::verify::project_verify_fact(proof,rt))]),
        MultivariableSelectorFailureStage::Selection {requirement,proof}=>object_for(rt,vec![("stage",string("selection")),("message",string("Requires a previously proved candidate or existence; WD does not calculate a limit or derivative.")),("requirement",string(requirement.readable_string())),("proof",super::verify::project_verify_fact(proof,rt))]),
    }
}

pub(super) fn strategy(
    p: &crate::execute::execute_fact_stmt::multivariable::strategy::MultivariableStrategyProof,
    rt: &Runtime,
) -> JsonValue {
    let p = p.stages();
    let geometry = interior(&p.geometry, rt);
    object_for(
        rt,
        vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("SmoothMultivariableExpression")),
            ("relation", string(p.relation.predicate_name())),
            (
                "function_domain",
                super::function_domain::project_source(&p.function_domain, rt),
            ),
            (
                "body_equal",
                super::searched::project_known_equality_path(&p.body_equal, rt),
            ),
            (
                "body_well_defined",
                super::wd::project_obj_wd_proof(&p.body_well_defined, rt),
            ),
            ("geometry", geometry),
            (
                "coordinates",
                JsonValue::Array(
                    p.coordinates
                        .iter()
                        .map(|c| {
                            object_for(
                                rt,
                                vec![
                                    ("row", string(c.row.to_string())),
                                    ("axis", string(c.first_axis.readable_string())),
                                    ("reduction", reduction(&c.reduction, rt)),
                                    ("first", smooth(&c.first, rt)),
                                    (
                                        "second",
                                        c.second
                                            .as_ref()
                                            .map(|p| smooth(p, rt))
                                            .unwrap_or(JsonValue::Null),
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            (
                "conclusions",
                JsonValue::Array(
                    p.conclusion_equalities
                        .iter()
                        .map(|e| {
                            object_for(
                                rt,
                                vec![
                                    ("target_reduction", reduction(&e.target_reduction, rt)),
                                    (
                                        "equality",
                                        super::verify::project_verify_fact(&e.equality, rt),
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
fn interior(
    p: &crate::execute::execute_fact_stmt::multivariable::strategy::MultivariableInteriorProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::multivariable::strategy::MultivariableInteriorProof;
    match p {
        MultivariableInteriorProof::ExactFiniteFunctionSpace {
            source,
            target,
            signature_equal,
            point_member,
        } => object_for(
            rt,
            vec![
                ("kind", string("exact_finite_function_space")),
                (
                    "source",
                    string(
                        crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(
                            source.clone(),
                        ))
                        .readable_string(),
                    ),
                ),
                (
                    "target",
                    string(
                        crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(
                            target.clone(),
                        ))
                        .readable_string(),
                    ),
                ),
                (
                    "signature_equal",
                    super::searched::project_equal_searched(signature_equal, rt),
                ),
                (
                    "point_member",
                    super::verify::project_verify_fact(point_member, rt),
                ),
            ],
        ),
        MultivariableInteriorProof::FullEuclideanSpace {
            domain_equal,
            point_member,
        } => object_for(
            rt,
            vec![
                ("kind", string("full_euclidean_space")),
                (
                    "domain_equal",
                    super::searched::project_equal_searched(domain_equal, rt),
                ),
                (
                    "point_member",
                    super::verify::project_verify_fact(point_member, rt),
                ),
            ],
        ),
        MultivariableInteriorProof::Known { condition, proof } => object_for(
            rt,
            vec![
                ("condition", string(condition.readable_string())),
                ("proof", super::verify::project_verify_fact(proof, rt)),
            ],
        ),
        MultivariableInteriorProof::OpenGuards {
            domain,
            base,
            guards,
        } => object_for(
            rt,
            vec![
                ("kind", string("stable_open_guards")),
                ("domain", string(domain.readable_string())),
                ("base", interior(base, rt)),
                (
                    "guards",
                    JsonValue::Array(
                        guards
                            .iter()
                            .map(|g| {
                                object_for(
                                    rt,
                                    vec![
                                        ("condition", string(g.point_condition.readable_string())),
                                        (
                                            "proof",
                                            super::verify::project_verify_fact(&g.point_proof, rt),
                                        ),
                                        (
                                            "operands",
                                            JsonValue::Array(
                                                g.operands.iter().map(|p| smooth(p, rt)).collect(),
                                            ),
                                        ),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                ),
            ],
        ),
    }
}
pub(super) fn reduction(
    p: &crate::execute::execute_fact_stmt::multivariable::expression::MultivariableReductionProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::multivariable::expression::MultivariableReductionStep;
    object_for(
        rt,
        vec![
            ("source", string(p.source.readable_string())),
            ("result", string(p.result.readable_string())),
            (
                "steps",
                JsonValue::Array(
                    p.steps
                        .iter()
                        .map(|s| match s {
                            MultivariableReductionStep::ExactRational { source, value } => {
                                object_for(
                                    rt,
                                    vec![
                                        ("kind", string("exact_rational")),
                                        ("source", string(source.readable_string())),
                                        ("value", string(value.readable_string())),
                                    ],
                                )
                            }
                            MultivariableReductionStep::PeriodicTrig { source, proof } => {
                                object_for(
                                    rt,
                                    vec![
                                        ("kind", string("periodic_trig")),
                                        ("source", string(source.readable_string())),
                                        (
                                            "coefficient",
                                            string(proof.coefficient.readable_string()),
                                        ),
                                        ("value", string(proof.value.readable_string())),
                                    ],
                                )
                            }
                            MultivariableReductionStep::NativeMatrixBeta { source, arguments } => {
                                object_for(
                                    rt,
                                    vec![
                                        ("kind", string("native_matrix_beta")),
                                        ("source", super::native_matrix::callable(source, rt)),
                                        (
                                            "arguments",
                                            JsonValue::Array(
                                                arguments
                                                    .iter()
                                                    .map(|a| string(a.readable_string()))
                                                    .collect(),
                                            ),
                                        ),
                                    ],
                                )
                            }
                            MultivariableReductionStep::FiniteSetEvaluation {
                                source,
                                left,
                                right,
                                value,
                            } => object_for(
                                rt,
                                vec![
                                    ("kind", string("finite_set_evaluation")),
                                    ("source", string(source.readable_string())),
                                    ("left_exact", string(left.to_obj().readable_string())),
                                    ("right_exact", string(right.to_obj().readable_string())),
                                    ("value", string(value.readable_string())),
                                ],
                            ),
                            MultivariableReductionStep::AnonymousBeta {
                                function,
                                arguments,
                            } => object_for(
                                rt,
                                vec![
                                    ("kind", string("anonymous_beta")),
                                    (
                                        "function",
                                        string(
                                            crate::ast::obj::Obj::FunctionSpace(
                                                crate::ast::obj::FunctionSpace::AnonymousFn(
                                                    function.clone(),
                                                ),
                                            )
                                            .readable_string(),
                                        ),
                                    ),
                                    (
                                        "arguments",
                                        JsonValue::Array(
                                            arguments
                                                .iter()
                                                .map(|a| string(a.readable_string()))
                                                .collect(),
                                        ),
                                    ),
                                ],
                            ),
                            MultivariableReductionStep::TupleProjection { index, .. } => {
                                object_for(
                                    rt,
                                    vec![
                                        ("kind", string("tuple_projection")),
                                        ("index", string(index.to_string())),
                                    ],
                                )
                            }
                        })
                        .collect(),
                ),
            ),
        ],
    )
}
fn smooth(
    p:&crate::execute::execute_fact_stmt::multivariable::expression::SmoothCoordinateExpressionProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::multivariable::expression::SmoothCoordinateConstructorProof as C;
    let mut fields = vec![
        ("expression", string(p.expression.readable_string())),
        (
            "value_source_well_defined",
            super::wd::project_obj_wd_proof(&p.value_source_well_defined, rt),
        ),
        (
            "derivative_source_well_defined",
            super::wd::project_obj_wd_proof(&p.derivative_source_well_defined, rt),
        ),
        ("value_reduction", reduction(&p.value_reduction, rt)),
        (
            "value_real",
            super::verify::project_verify_fact(&p.value_real, rt),
        ),
        (
            "derivative_expression",
            string(p.derivative_expression.readable_string()),
        ),
        (
            "derivative_reduction",
            reduction(&p.derivative_reduction, rt),
        ),
        (
            "derivative_real",
            super::verify::project_verify_fact(&p.derivative_real, rt),
        ),
    ];
    let constructor = match &p.constructor {
        C::Constant => "constant",
        C::Coordinate {
            index,
            index_member,
            axis_comparison,
        } => {
            fields.push(("index", string(index.readable_string())));
            fields.push((
                "index_member",
                super::verify::project_verify_fact(index_member, rt),
            ));
            fields.push((
                "axis_comparison",
                super::verify::project_verify_fact(axis_comparison, rt),
            ));
            "coordinate"
        }
        C::Neg { argument } => {
            fields.push(("argument", smooth(argument, rt)));
            "neg"
        }
        C::Add { left, right } | C::Subtract { left, right } | C::Multiply { left, right } => {
            fields.push(("left", smooth(left, rt)));
            fields.push(("right", smooth(right, rt)));
            match &p.constructor {
                C::Add { .. } => "add",
                C::Subtract { .. } => "subtract",
                _ => "multiply",
            }
        }
        C::Divide {
            left,
            right,
            nonzero,
        } => {
            fields.push(("left", smooth(left, rt)));
            fields.push(("right", smooth(right, rt)));
            fields.push(("nonzero", super::verify::project_verify_fact(nonzero, rt)));
            "divide"
        }
        C::NaturalPower {
            base,
            exponent_natural,
        } => {
            fields.push(("base", smooth(base, rt)));
            fields.push((
                "exponent_natural",
                super::verify::project_verify_fact(exponent_natural, rt),
            ));
            "natural_power"
        }
        C::Elementary {
            kind,
            argument,
            domain,
        } => {
            fields.push(("function", string(kind.name())));
            fields.push(("argument", smooth(argument, rt)));
            fields.push(("domain", super::verify::project_verify_fact(domain, rt)));
            "elementary"
        }
    };
    fields.push(("constructor", string(constructor)));
    object_for(rt, fields)
}
