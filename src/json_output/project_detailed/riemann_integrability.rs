//! Scoped integrability certificates retain their closure and continuity premises.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::riemann_integrability::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project(p: &RiemannIntegrabilityProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("RiemannIntegrability")),
            ("function", string(p.function.readable_string())),
            ("lower", string(p.lower.readable_string())),
            ("upper", string(p.upper.readable_string())),
            ("domain", super::function_limit::domain(&p.domain, rt)),
            (
                "interval_requirements",
                super::store::project_verify_facts(&p.interval_requirements, rt),
            ),
            (
                "source",
                match &p.source {
                    RiemannIntegrabilitySource::Defined {
                        body,
                        equality,
                        well_defined,
                    } => object_for(
                        rt,
                        vec![
                            ("kind", string("Defined")),
                            (
                                "body",
                                string(
                                    crate::ast::obj::Obj::FunctionSpace(
                                        crate::ast::obj::FunctionSpace::AnonymousFn(body.clone()),
                                    )
                                    .readable_string(),
                                ),
                            ),
                            (
                                "body_equal",
                                super::searched::project_known_equality_path(equality, rt),
                            ),
                            (
                                "body_well_defined",
                                super::function_domain::project_checked_body(well_defined, rt),
                            ),
                        ],
                    ),
                    RiemannIntegrabilitySource::Applied { parameter } => object_for(
                        rt,
                        vec![
                            ("kind", string("Applied")),
                            (
                                "parameter",
                                string(
                                    crate::ast::obj::Obj::Identifier(
                                        crate::ast::obj::IdentifierObj::from_bound_name(parameter),
                                    )
                                    .readable_string(),
                                ),
                            ),
                        ],
                    ),
                },
            ),
            (
                "interval_stores",
                JsonValue::Array(
                    p.interval_stores
                        .iter()
                        .map(|proof| super::store::project_store_and_infer(proof, rt))
                        .collect(),
                ),
            ),
            (
                "introduced_point",
                super::verify::project_introduced_params(&p.introduced_point, rt),
            ),
            (
                "continuity_premises",
                JsonValue::Array(
                    p.continuity_premises
                        .iter()
                        .map(|premise| {
                            object_for(
                                rt,
                                vec![
                                    ("fact", string(premise.fact.readable_string())),
                                    (
                                        "interval_continuity",
                                        project_verify_fact(&premise.interval_continuity, rt),
                                    ),
                                    (
                                        "point_membership",
                                        project_verify_fact(&premise.point_membership, rt),
                                    ),
                                    (
                                        "store",
                                        super::store::project_store_and_infer(&premise.store, rt),
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            ("expression", expression(&p.expression, rt)),
        ],
    )
}

fn expression(p: &RiemannIntegrableExpressionProof, rt: &Runtime) -> JsonValue {
    use RiemannIntegrableConstructorProof as C;
    let constructor = match &p.constructor {
        C::Constant => object_for(rt, vec![("rule", string("Constant"))]),
        C::Variable => object_for(rt, vec![("rule", string("Variable"))]),
        C::Neg { argument } | C::Abs { argument } => object_for(
            rt,
            vec![
                (
                    "rule",
                    string(if matches!(p.constructor, C::Neg { .. }) {
                        "Neg"
                    } else {
                        "Abs"
                    }),
                ),
                ("argument", expression(argument, rt)),
            ],
        ),
        C::Add { left, right } | C::Sub { left, right } | C::Mul { left, right } => object_for(
            rt,
            vec![
                (
                    "rule",
                    string(match p.constructor {
                        C::Add { .. } => "Add",
                        C::Sub { .. } => "Sub",
                        _ => "Mul",
                    }),
                ),
                ("left", expression(left, rt)),
                ("right", expression(right, rt)),
            ],
        ),
        C::NaturalPower {
            base,
            exponent_natural,
        } => object_for(
            rt,
            vec![
                ("rule", string("NaturalPower")),
                ("base", expression(base, rt)),
                (
                    "exponent_natural",
                    project_verify_fact(exponent_natural, rt),
                ),
            ],
        ),
        C::Quotient {
            numerator,
            denominator_continuity,
            denominator_nonzero,
        } => object_for(
            rt,
            vec![
                ("rule", string("QuotientContinuousDenominator")),
                ("numerator", expression(numerator, rt)),
                (
                    "denominator_continuity",
                    super::pointwise_continuity::expression(denominator_continuity, rt),
                ),
                (
                    "denominator_nonzero",
                    project_verify_fact(denominator_nonzero, rt),
                ),
            ],
        ),
        C::Application {
            function,
            integrability,
        } => object_for(
            rt,
            vec![
                ("rule", string("Application")),
                ("function", string(function.readable_string())),
                ("integrability", project_verify_fact(integrability, rt)),
            ],
        ),
        C::Continuous(proof) => object_for(
            rt,
            vec![
                ("rule", string("ContinuousOnCompactInterval")),
                (
                    "continuity",
                    super::pointwise_continuity::expression(proof, rt),
                ),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("expression", string(p.expression.readable_string())),
            ("value_at_point", string(p.value.readable_string())),
            ("value_real", project_verify_fact(&p.value_real, rt)),
            ("constructor", constructor),
        ],
    )
}
