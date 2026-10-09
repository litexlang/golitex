use crate::prelude::*;

// Preserve the existing decimal leaf, then exact fractions and complex
// coordinates. Symbolic monomial normalization deliberately stays in Builtin.
pub(crate) fn calculate_value_pair(left: &Obj, right: &Obj) -> Option<(ClosedValuePair, bool)> {
    if let (Some(left), Some(right)) = (
        calculate_closed_decimal(left),
        calculate_closed_decimal(right),
    ) {
        let equal = left.normalized_value == right.normalized_value;
        return Some((
            ClosedValuePair::Decimal {
                left: left.normalized_value,
                right: right.normalized_value,
            },
            equal,
        ));
    }
    if let (Some(left), Some(right)) = (EvalRational::from_obj(left), EvalRational::from_obj(right))
    {
        let equal = left == right;
        return Some((ClosedValuePair::Rational { left, right }, equal));
    }
    if let (Some(left), Some(right)) = (
        crate::rational_expression::exact_radical::ExactRadical::from_obj(left),
        crate::rational_expression::exact_radical::ExactRadical::from_obj(right),
    ) {
        let equal = left == right;
        return Some((
            ClosedValuePair::Radical {
                left_normal: left.to_obj(),
                right_normal: right.to_obj(),
            },
            equal,
        ));
    }
    let (left_real, left_imaginary) = exact_complex_coordinates(left)?;
    let (right_real, right_imaginary) = exact_complex_coordinates(right)?;
    let equal = left_real == right_real && left_imaginary == right_imaginary;
    Some((
        ClosedValuePair::Complex {
            left_real,
            left_imaginary,
            right_real,
            right_imaginary,
        },
        equal,
    ))
}

// The general evaluator also handles tuple dimensions and finite-set sizes,
// including trees containing symbolic children. Only its classified numeric
// subset belongs in this closed leaf; keep those structural rules above Direct.
pub(crate) fn calculate_closed_decimal(obj: &Obj) -> Option<Number> {
    if !is_closed_numeric_expr(obj) {
        return None;
    }
    evaluate_obj_to_normalized_decimal_number(obj)
}
