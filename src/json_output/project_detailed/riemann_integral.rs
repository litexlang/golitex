//! Integral WD exposes checked interval coverage and integrability evidence.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::riemann_integral::*;
use crate::execute::execute_fact_stmt::structural_riemann_integral::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn structural(p: &StructuralRiemannIntegralProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("StructuralRiemannIntegral")),
            ("function", string(p.function.readable_string())),
            ("lower", string(p.lower.readable_string())),
            ("upper", string(p.upper.readable_string())),
            ("domain", super::function_limit::domain(&p.domain, rt)),
            (
                "interval_requirements",
                super::store::project_verify_facts(&p.interval_requirements, rt),
            ),
            (
                "body",
                string(
                    crate::ast::obj::Obj::FunctionSpace(
                        crate::ast::obj::FunctionSpace::AnonymousFn(p.body.clone()),
                    )
                    .readable_string(),
                ),
            ),
            (
                "body_equal",
                super::searched::project_known_equality_path(&p.body_equal, rt),
            ),
            (
                "body_well_defined",
                super::function_domain::project_checked_body(&p.body_well_defined, rt),
            ),
            ("expression", expression(&p.expression, rt)),
            (
                "conclusion",
                match &p.conclusion {
                    RiemannConclusionProof::Candidate(proof) => project_verify_fact(proof, rt),
                    RiemannConclusionProof::Integrable => {
                        object_for(rt, vec![("rule", string("RiemannCandidateExistence"))])
                    }
                },
            ),
        ],
    )
}

fn expression(p: &RiemannExpressionProof, rt: &Runtime) -> JsonValue {
    use RiemannConstructorProof as C;
    let constructor = match &p.constructor {
        C::Polynomial {
            equality,
            normalized,
        } => object_for(
            rt,
            vec![
                ("rule", string("PolynomialNormalization")),
                ("pointwise_equality", project_verify_fact(equality, rt)),
                ("normalized_integral", expression(normalized, rt)),
            ],
        ),
        C::Constant { value_real } => object_for(
            rt,
            vec![
                ("rule", string("Constant")),
                ("value_real", project_verify_fact(value_real, rt)),
            ],
        ),
        C::Variable => object_for(rt, vec![("rule", string("Variable"))]),
        C::NaturalPower { exponent_natural } => object_for(
            rt,
            vec![
                ("rule", string("NaturalPower")),
                (
                    "exponent_natural",
                    project_verify_fact(exponent_natural, rt),
                ),
            ],
        ),
        C::Neg { argument } => object_for(
            rt,
            vec![
                ("rule", string("Neg")),
                ("argument", expression(argument, rt)),
            ],
        ),
        C::Add { left, right } | C::Sub { left, right } => object_for(
            rt,
            vec![
                (
                    "rule",
                    string(if matches!(p.constructor, C::Add { .. }) {
                        "Add"
                    } else {
                        "Sub"
                    }),
                ),
                ("left", expression(left, rt)),
                ("right", expression(right, rt)),
            ],
        ),
        C::Scale {
            scalar,
            scalar_real,
            argument,
        } => object_for(
            rt,
            vec![
                ("rule", string("Scale")),
                ("scalar", string(scalar.readable_string())),
                ("scalar_real", project_verify_fact(scalar_real, rt)),
                ("argument", expression(argument, rt)),
            ],
        ),
        C::Divide {
            argument,
            denominator_real,
            denominator_nonzero,
        } => object_for(
            rt,
            vec![
                ("rule", string("Divide")),
                ("argument", expression(argument, rt)),
                (
                    "denominator_real",
                    project_verify_fact(denominator_real, rt),
                ),
                (
                    "denominator_nonzero",
                    project_verify_fact(denominator_nonzero, rt),
                ),
            ],
        ),
        C::Application { function, leaf } => object_for(
            rt,
            vec![
                ("rule", string("Application")),
                ("function", string(function.readable_string())),
                (
                    "leaf",
                    match leaf {
                        RiemannLeafProof::Candidate(proof) => {
                            super::searched::project_known_premise(proof, rt)
                        }
                        RiemannLeafProof::Selected {
                            integrability,
                            value_well_defined,
                        } => object_for(
                            rt,
                            vec![
                                ("integrability", project_verify_fact(integrability, rt)),
                                (
                                    "value_well_defined",
                                    super::wd::project_obj_wd_proof(value_well_defined, rt),
                                ),
                            ],
                        ),
                    },
                ),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("expression", string(p.expression.readable_string())),
            ("integral", string(p.integral.readable_string())),
            ("constructor", constructor),
            ("integral_real", project_verify_fact(&p.integral_real, rt)),
        ],
    )
}

pub(super) fn object_wd(p: &RiemannIntegralWellDefinedProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("by_def")),
            ("family", string("IntegralOperator")),
            ("kind", string("Riemann")),
            (
                "function_wd",
                super::wd::project_obj_wd_proof(&p.function_wd, rt),
            ),
            ("lower_wd", super::wd::project_obj_wd_proof(&p.lower_wd, rt)),
            ("upper_wd", super::wd::project_obj_wd_proof(&p.upper_wd, rt)),
            (
                "function_domain",
                super::function_limit::domain(&p.domain, rt),
            ),
            (
                "requirements",
                JsonValue::Array(
                    p.requirements
                        .iter()
                        .map(|r| {
                            object_for(
                                rt,
                                vec![
                                    ("requirement", string(r.requirement.readable_string())),
                                    (
                                        "proof",
                                        super::wd::project_predicate_requirement(&r.result, rt),
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            ("integrability", project_verify_fact(&p.integrability, rt)),
        ],
    )
}
pub(super) fn object_failure(p: &RiemannIntegralWellDefinedFailure, rt: &Runtime) -> JsonValue {
    let stage = match &p.stage {
        RiemannIntegralFailureStage::Domain => object_for(
            rt,
            vec![
                ("stage", string("domain")),
                (
                    "message",
                    string("Requires a complete unary real function."),
                ),
            ],
        ),
        RiemannIntegralFailureStage::Requirement {
            requirement,
            result,
        } => object_for(
            rt,
            vec![
                ("stage", string("interval_domain")),
                ("requirement", string(requirement.readable_string())),
                ("proof", project_verify_fact(result, rt)),
            ],
        ),
        RiemannIntegralFailureStage::Selection(result) => object_for(
            rt,
            vec![
                ("stage", string("proved_integrability")),
                (
                    "message",
                    string(
                        "Could not prove finite Riemann integrability on the requested interval.",
                    ),
                ),
                ("requirement", project_verify_fact(result, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("type", string("obj_well_defined_failure")),
            ("kind", string("RiemannIntegral")),
            ("obj", string(p.obj.readable_string())),
            ("reason", stage),
        ],
    )
}
