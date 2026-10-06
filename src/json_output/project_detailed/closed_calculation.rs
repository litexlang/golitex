use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::closed_calculation_proof::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::rational_expression::NumberCompareResult;
use crate::runtime::Runtime;

pub(super) fn project_equal_calculation(
    proof: &ClosedEqualityCalculationProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("type", string("by_closed_calculation")),
            ("kind", string("equal")),
            ("values", project_values(&proof.values, runtime)),
        ],
    )
}

fn project_values(values: &ClosedValuePair, runtime: &Runtime) -> JsonValue {
    match values {
        ClosedValuePair::Radical { left_normal, right_normal } => object_for(runtime, vec![
            ("representation", string("radical")),
            ("left_normal", string(left_normal.readable_string())),
            ("right_normal", string(right_normal.readable_string())),
        ]),
        ClosedValuePair::Decimal { left, right } => object_for(
            runtime,
            vec![
                ("representation", string("decimal")),
                ("left_normal", string(left)),
                ("right_normal", string(right)),
            ],
        ),
        ClosedValuePair::Rational { left, right } => object_for(
            runtime,
            vec![
                ("representation", string("rational")),
                ("left_normal", string(left.to_obj().readable_string())),
                ("right_normal", string(right.to_obj().readable_string())),
            ],
        ),
        ClosedValuePair::Complex {
            left_real,
            left_imaginary,
            right_real,
            right_imaginary,
        } => object_for(
            runtime,
            vec![
                ("representation", string("complex")),
                ("left_real", string(left_real.to_obj().readable_string())),
                (
                    "left_imaginary",
                    string(left_imaginary.to_obj().readable_string()),
                ),
                ("right_real", string(right_real.to_obj().readable_string())),
                (
                    "right_imaginary",
                    string(right_imaginary.to_obj().readable_string()),
                ),
            ],
        ),
    }
}

pub(super) fn project_atomic_calculation(
    proof: &ClosedAtomicExceptEqualityCalculationProof,
    runtime: &Runtime,
) -> JsonValue {
    use ClosedAtomicExceptEqualityCalculationProof::*;
    match proof {
        NotEqual(p) => object_for(
            runtime,
            vec![
                ("type", string("by_closed_calculation")),
                ("kind", string("not_equal")),
                ("values", project_values(&p.values, runtime)),
            ],
        ),
        Less(p) => project_comparison("less", p, runtime),
        Greater(p) => project_comparison("greater", p, runtime),
        LessEqual(p) => project_comparison("less_equal", p, runtime),
        GreaterEqual(p) => project_comparison("greater_equal", p, runtime),
        NotLess(p) => project_comparison("not_less", p, runtime),
        NotGreater(p) => project_comparison("not_greater", p, runtime),
        NotLessEqual(p) => project_comparison("not_less_equal", p, runtime),
        NotGreaterEqual(p) => project_comparison("not_greater_equal", p, runtime),
        In(p) => project_membership("in", p, runtime),
        NotIn(p) => project_membership("not_in", p, runtime),
    }
}

fn project_comparison(
    kind: &str,
    proof: &ClosedComparisonCalculationProof,
    runtime: &Runtime,
) -> JsonValue {
    let comparison = match proof.comparison {
        NumberCompareResult::Less => "less",
        NumberCompareResult::Equal => "equal",
        NumberCompareResult::Greater => "greater",
    };
    object_for(
        runtime,
        vec![
            ("type", string("by_closed_calculation")),
            ("kind", string(kind)),
            ("left_normal", string(&proof.left_normal)),
            ("right_normal", string(&proof.right_normal)),
            ("comparison", string(comparison)),
        ],
    )
}

pub(super) fn project_membership(
    kind: &str,
    proof: &ClosedMembershipCalculationProof,
    runtime: &Runtime,
) -> JsonValue {
    let (value, set, bounds) = match proof {
        ClosedMembershipCalculationProof::StandardSet { value, set } =>
            (value, Obj::StandardSet(set.clone()), None),
        ClosedMembershipCalculationProof::IntegerRange { value, set, start, end } =>
            (value, set.clone(), Some((start, end))),
    };
    let mut fields = vec![
        ("type", string("by_closed_calculation")),
        ("kind", string(kind)),
        ("value", project_scalar(value, runtime)),
        ("set", string(set.readable_string())),
    ];
    if let Some((start, end)) = bounds {
        fields.push(("bounds", JsonValue::Array(vec![project_scalar(start, runtime), project_scalar(end, runtime)])));
    }
    object_for(runtime, fields)
}

fn project_scalar(value: &ClosedScalarValue, runtime: &Runtime) -> JsonValue {
    match value {
        ClosedScalarValue::Decimal(normal) => object_for(
            runtime,
            vec![
                ("representation", string("decimal")),
                ("normal", string(normal)),
            ],
        ),
        ClosedScalarValue::ExactComplex { real, imaginary } => object_for(
            runtime,
            vec![
                ("representation", string("exact_complex")),
                ("real", string(real.to_obj().readable_string())),
                ("imaginary", string(imaginary.to_obj().readable_string())),
            ],
        ),
    }
}
