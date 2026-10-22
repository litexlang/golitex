//! Pointwise continuity certificates, including the actual composed centres.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::pointwise_continuity::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_pointwise_continuity(
    p: &PointwiseContinuityProof,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("PointwiseContinuity")),
            ("function", string(p.function.readable_string())),
            ("point", string(p.point.readable_string())),
            ("domain", string(p.domain.domain.readable_string())),
            (
                "complete_source",
                super::function_domain::project_source(&p.domain.source, rt),
            ),
            ("input_real", project_verify_fact(&p.domain.input_real, rt)),
            (
                "output_real",
                project_verify_fact(&p.domain.output_real, rt),
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
                super::wd::project_obj_wd_proof(&p.body_well_defined, rt),
            ),
            ("expression", expression(&p.expression, rt)),
        ],
    )
}
pub(super) fn expression(p: &PointwiseContinuityExpressionProof, rt: &Runtime) -> JsonValue {
    use PointwiseContinuityConstructorProof as C;
    let mut fields = vec![
        ("expression", string(p.expression.readable_string())),
        ("value_at_point", string(p.value.readable_string())),
        ("value_real", project_verify_fact(&p.value_real, rt)),
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
            "ElementaryContinuity"
        }
        C::Constant => "Constant",
        C::Variable => "Identity",
        C::Neg { argument } => {
            fields.push(("argument", expression(argument, rt)));
            "Neg"
        }
        C::Abs { argument } => {
            fields.push(("argument", expression(argument, rt)));
            "Abs"
        }
        C::Add { left, right } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            "Add"
        }
        C::Sub { left, right } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            "Sub"
        }
        C::Mul { left, right } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            "Mul"
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
            "Divide"
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
            outer_continuity,
        } => {
            fields.push(("outer_function", string(function.readable_string())));
            fields.push(("outer_point", string(argument.value.readable_string())));
            fields.push(("argument", expression(argument, rt)));
            fields.push((
                "outer_continuity",
                project_verify_fact(outer_continuity, rt),
            ));
            "Compose"
        }
    };
    fields.push(("rule", string(rule)));
    object_for(rt, fields)
}
