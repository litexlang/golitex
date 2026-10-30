//! Typed structural-limit certificates; no theorem execution or opaque Debug payload.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::structural_limit::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof;
use crate::json_output::helper::{object_for, string};
use crate::prelude::*;

pub(super) fn project(p: &StructuralLimitProof, rt: &Runtime) -> JsonValue {
    let (direction, point) = match &p.approach {
        StructuralLimitApproach::Sequence => ("sequence", JsonValue::Null),
        StructuralLimitApproach::Function(approach) => {
            let name = match approach {
                LimitApproach::AtPoint(_) => "at",
                LimitApproach::FromLeft(_) => "left",
                LimitApproach::FromRight(_) => "right",
                LimitApproach::AtNegativeInfinity => "neg_inf",
                LimitApproach::AtPositiveInfinity => "pos_inf",
            };
            (
                name,
                approach
                    .point()
                    .map(|x| string(x.readable_string()))
                    .unwrap_or(JsonValue::Null),
            )
        }
    };
    let geometry = match &p.geometry {
        StructuralLimitGeometryProof::PositiveNaturalSequence => {
            object_for(rt, vec![("rule", string("PositiveNaturalSequence"))])
        }
        StructuralLimitGeometryProof::RealLine {
            domain_equal,
            approach_real,
        } => {
            let point_real = match approach_real {
                FunctionLimitApproachRealProof::Finite(proof) => project_verify_fact(proof, rt),
                FunctionLimitApproachRealProof::AtNegativeInfinity => string("negative_infinity"),
                FunctionLimitApproachRealProof::AtPositiveInfinity => string("positive_infinity"),
            };
            object_for(
                rt,
                vec![
                    ("rule", string("RealLineAccumulation")),
                    (
                        "domain_equal",
                        super::searched::project_equal_searched(domain_equal, rt),
                    ),
                    ("approach_real", point_real),
                ],
            )
        }
        StructuralLimitGeometryProof::EstablishedCandidate {
            domain: source,
            candidate,
        } => object_for(
            rt,
            vec![
                ("rule", string("AccumulationFromCandidate")),
                ("source_domain", domain(source, rt)),
                (
                    "candidate",
                    super::searched::project_known_premise(candidate, rt),
                ),
            ],
        ),
        StructuralLimitGeometryProof::Known { requirement, proof } => object_for(
            rt,
            vec![
                ("requirement", string(requirement.readable_string())),
                ("proof", project_verify_fact(proof, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("StructuralLimit")),
            ("function", string(p.function.readable_string())),
            ("direction", string(direction)),
            ("point", point),
            ("complete_domain", domain(&p.domain, rt)),
            (
                "body",
                string(
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(p.body.clone()))
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
            ("geometry", geometry),
            ("expression", expression(&p.expression, rt)),
            ("result_equal", project_verify_fact(&p.result_equal, rt)),
        ],
    )
}

fn domain(
    p: &crate::execute::execute_fact_stmt::function_limit::RealFunctionLimitDomainProof,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("domain", string(p.domain.readable_string())),
            (
                "source",
                super::function_domain::project_source(&p.source, rt),
            ),
            ("input_real", project_verify_fact(&p.input_real, rt)),
            ("output_real", project_verify_fact(&p.output_real, rt)),
        ],
    )
}

fn expression(p: &StructuralLimitExpressionProof, rt: &Runtime) -> JsonValue {
    use StructuralLimitConstructorProof as C;
    let mut fields = vec![
        ("expression", string(p.expression.readable_string())),
        ("limit", string(p.limit.readable_string())),
    ];
    let rule = match &p.constructor {
        C::Constant => "Constant",
        C::FiniteIdentity => "FiniteIdentity",
        C::Candidate {
            function_domain,
            candidate,
        } => {
            fields.push(("function_domain", domain(function_domain, rt)));
            fields.push((
                "candidate",
                super::searched::project_known_premise(candidate, rt),
            ));
            "LimitCandidate"
        }
        C::SequenceShift {
            function_domain,
            candidate,
            offset,
            offset_natural,
        } => {
            fields.push(("function_domain", domain(function_domain, rt)));
            fields.push(("offset", string(offset.readable_string())));
            fields.push(("offset_natural", project_verify_fact(offset_natural, rt)));
            fields.push((
                "candidate",
                super::searched::project_known_premise(candidate, rt),
            ));
            "SequenceShift"
        }
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
            "Subtract"
        }
        C::Mul { left, right } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            "Multiply"
        }
        C::Div {
            left,
            right,
            limit_nonzero,
        } => {
            fields.push(("left", expression(left, rt)));
            fields.push(("right", expression(right, rt)));
            fields.push(("limit_nonzero", project_verify_fact(limit_nonzero, rt)));
            "Divide"
        }
        C::NaturalPower {
            base,
            exponent,
            exponent_natural,
        } => {
            fields.push(("exponent", string(exponent.readable_string())));
            fields.push((
                "exponent_natural",
                project_verify_fact(exponent_natural, rt),
            ));
            fields.push(("base", expression(base, rt)));
            "NaturalPower"
        }
    };
    fields.push(("rule", string(rule)));
    fields.push(("limit_real", project_verify_fact(&p.limit_real, rt)));
    object_for(rt, fields)
}
