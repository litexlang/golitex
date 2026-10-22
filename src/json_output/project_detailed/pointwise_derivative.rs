//! Recursive first derivative and open-neighbourhood certificates.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::pointwise_derivative::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
pub(super) fn project(p: &PointwiseDerivativeProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PointwiseDerivative")),
            ("function", string(p.function.readable_string())),
            ("point", string(p.point.readable_string())),
            ("domain", super::function_limit::domain(&p.domain, rt)),
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
                super::wd::project_obj_wd_proof(&p.body_well_defined, rt),
            ),
            ("interior", interior(&p.interior, rt)),
            ("expression", expression(&p.expression, rt)),
            (
                "conclusion",
                match &p.conclusion {
                    DerivativeConclusionProof::Candidate(eq) => project_verify_fact(eq, rt),
                    DerivativeConclusionProof::Differentiable => {
                        object_for(rt, vec![("rule", string("DerivativeCandidateExistence"))])
                    }
                },
            ),
        ],
    )
}
fn interior(p: &PointInteriorProof, rt: &Runtime) -> JsonValue {
    match p {
        PointInteriorProof::Known { condition, proof } => object_for(
            rt,
            vec![
                ("rule", string("KnownInterior")),
                ("condition", string(condition.readable_string())),
                ("proof", project_verify_fact(proof, rt)),
            ],
        ),
        PointInteriorProof::StandardOpen {
            set,
            domain_equal,
            point_member,
        } => object_for(
            rt,
            vec![
                ("rule", string("StandardOpenRealSet")),
                (
                    "set",
                    string(crate::ast::obj::Obj::StandardSet(set.clone()).readable_string()),
                ),
                (
                    "domain_equal",
                    super::searched::project_equal_searched(domain_equal, rt),
                ),
                ("point_member", project_verify_fact(point_member, rt)),
            ],
        ),
        PointInteriorProof::Guarded {
            base,
            point_member,
            guards,
        } => object_for(
            rt,
            vec![
                ("rule", string("StableOpenGuards")),
                ("base", interior(base, rt)),
                ("point_member", project_verify_fact(point_member, rt)),
                (
                    "guards",
                    JsonValue::Array(
                        guards
                            .iter()
                            .map(|g| {
                                object_for(
                                    rt,
                                    vec![
                                        ("guard", string(g.guard.readable_string())),
                                        ("stability_rule", string(if matches!(g.guard, crate::ast::fact::AtomicFact::LessEqualFact(_) | crate::ast::fact::AtomicFact::GreaterEqualFact(_)) { "strict_margin_for_weak_guard" } else { "open_guard" })),
                                        ("point_fact", string(g.point_fact.readable_string())),
                                        ("point_proof", project_verify_fact(&g.point_proof, rt)),
                                        (
                                            "operands",
                                            JsonValue::Array(
                                                g.operands
                                                    .iter()
                                                    .map(|p| match p {
                                                        InteriorOperandProof::Continuous(p) => {
                                                            super::pointwise_continuity::expression(
                                                                p, rt,
                                                            )
                                                        }
                                                        InteriorOperandProof::Differentiable(p) => {
                                                            expression(p, rt)
                                                        }
                                                    })
                                                    .collect(),
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
fn expression(p: &DerivativeExpressionProof, rt: &Runtime) -> JsonValue {
    use DerivativeConstructorProof as C;
    let mut fields = vec![
        ("expression", string(p.expression.readable_string())),
        ("value_at_point", string(p.value.readable_string())),
        ("value_real", project_verify_fact(&p.value_real, rt)),
        (
            "derivative_candidate",
            string(p.derivative.readable_string()),
        ),
        (
            "derivative_real",
            project_verify_fact(&p.derivative_real, rt),
        ),
    ];
    let rule = match &p.constructor {
        C::Elementary {
            kind,
            argument,
            domain,
        } => {
            fields.push(("function", string(kind.name())));
            fields.push(("argument", expression(argument, rt)));
            fields.push(("analytic_domain", project_verify_fact(domain, rt)));
            "ElementaryChainRule"
        }
        C::Constant => "Constant",
        C::Variable => "Identity",
        C::Neg { argument } => {
            fields.push(("argument", expression(argument, rt)));
            "Neg"
        }
        C::Add { left, right } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            "Add"
        }
        C::Sub { left, right } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            "Subtract"
        }
        C::Mul { left, right } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            "ProductRule"
        }
        C::Div {
            left,
            right,
            denominator_nonzero,
        } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            fields.push((
                "denominator_nonzero",
                project_verify_fact(denominator_nonzero, rt),
            ));
            "QuotientRule"
        }
        C::NaturalPower {
            base,
            exponent_natural,
        } => {
            fields.push(("base", expression(base, rt)));
            fields.push((
                "exponent_natural",
                project_verify_fact(exponent_natural, rt),
            ));
            "NaturalPower"
        }
        C::Compose {
            function,
            argument,
            outer,
        } => {
            fields.push(("outer_function", string(function.readable_string())));
            fields.push(("outer_point", string(argument.value.readable_string())));
            fields.push(("argument", expression(argument, rt)));
            fields.push((
                "outer_derivative",
                match outer {
                    DerivativeLeafProof::Candidate(p) => {
                        super::searched::project_known_premise(p, rt)
                    }
                    DerivativeLeafProof::Selected {
                        differentiability,
                        value_well_defined,
                    } => object_for(
                        rt,
                        vec![
                            (
                                "differentiability",
                                project_verify_fact(differentiability, rt),
                            ),
                            (
                                "value_well_defined",
                                super::wd::project_obj_wd_proof(value_well_defined, rt),
                            ),
                        ],
                    ),
                },
            ));
            "ChainRule"
        }
    };
    fields.push(("rule", string(rule)));
    object_for(rt, fields)
}
