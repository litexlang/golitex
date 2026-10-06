use super::closed_calculation_proof::*;
use crate::ast::fact::AtomicFact;
use crate::ast::obj::{Literal, Number, Obj, SetFormer, StandardSet};
use crate::rational_expression::closed_scalar_membership::{
    exact_complex_inhabits_standard_set, normalized_decimal_inhabits_standard_set,
};
use crate::rational_expression::exact_complex::exact_complex_coordinates;
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::{
    compare_number_strings, evaluate_obj_to_normalized_decimal_number, is_closed_numeric_expr,
    NumberCompareResult,
};

// This leaf has no Runtime, VerifyState or search callback. It only evaluates
// finite closed ASTs. False, unsupported, undefined and overflowing calculations
// return no certificate. WD remains mandatory at the outer verify boundary.
pub fn calculate_closed_atomic_fact(fact: &AtomicFact) -> Option<ClosedCalculationProof> {
    use AtomicFact::*;
    use ClosedAtomicExceptEqualityCalculationProof as P;
    use NumberCompareResult::{Equal, Greater, Less};

    let proof = match fact {
        EqualFact(f) => {
            let (values, equal) = calculate_value_pair(&f.left, &f.right)?;
            return equal.then_some(ClosedCalculationProof::Equality(
                ClosedEqualityCalculationProof { values },
            ));
        }
        NotEqualFact(f) => {
            let (values, equal) = calculate_value_pair(&f.left, &f.right)?;
            if equal {
                return None;
            }
            P::NotEqual(ClosedNotEqualCalculationProof { values })
        }
        LessFact(f) => P::Less(calculate_comparison(&f.left, &f.right, &[Less])?),
        GreaterFact(f) => P::Greater(calculate_comparison(&f.left, &f.right, &[Greater])?),
        LessEqualFact(f) => P::LessEqual(calculate_comparison(&f.left, &f.right, &[Less, Equal])?),
        GreaterEqualFact(f) => {
            P::GreaterEqual(calculate_comparison(&f.left, &f.right, &[Greater, Equal])?)
        }
        NotLessFact(f) => P::NotLess(calculate_comparison(&f.left, &f.right, &[Greater, Equal])?),
        NotGreaterFact(f) => {
            P::NotGreater(calculate_comparison(&f.left, &f.right, &[Less, Equal])?)
        }
        NotLessEqualFact(f) => {
            P::NotLessEqual(calculate_comparison(&f.left, &f.right, &[Greater])?)
        }
        NotGreaterEqualFact(f) => {
            P::NotGreaterEqual(calculate_comparison(&f.left, &f.right, &[Less])?)
        }
        InFact(f) => P::In(calculate_membership(&f.element, &f.set, true)?),
        NotInFact(f) => P::NotIn(calculate_membership(&f.element, &f.set, false)?),
        // Explicitly unsupported families: calculation does not unfold a
        // predicate or generate structural/set-theoretic proof obligations.
        NormalAtomicFact(_)
        | NotNormalAtomicFact(_)
        | IsSetFact(_)
        | NotIsSetFact(_)
        | IsNonemptySetFact(_)
        | NotIsNonemptySetFact(_)
        | IsFiniteSetFact(_)
        | NotIsFiniteSetFact(_)
        | IsCartFact(_)
        | NotIsCartFact(_)
        | IsTupleFact(_)
        | NotIsTupleFact(_)
        | SubsetFact(_)
        | NotSubsetFact(_)
        | SupersetFact(_)
        | NotSupersetFact(_)
        | ProperSubsetFact(_)
        | NotProperSubsetFact(_)
        | ProperSupersetFact(_)
        | NotProperSupersetFact(_)
        | PrimeFact(_)
        | NotPrimeFact(_)
        | CoprimeFact(_)
        | NotCoprimeFact(_)
        | DvdFact(_)
        | NotDvdFact(_)
        | InjectiveFact(_)
        | NotInjectiveFact(_)
        | SurjectiveFact(_)
        | NotSurjectiveFact(_)
        | BijectiveFact(_)
        | NotBijectiveFact(_)
        | IsChoiceFunctionForFact(_)
        | NotIsChoiceFunctionForFact(_) => return None,
    };
    Some(ClosedCalculationProof::AtomicExceptEquality(proof))
}

// Preserve the existing decimal leaf, then exact fractions and complex
// coordinates. Symbolic monomial normalization deliberately stays in Builtin.
fn calculate_value_pair(left: &Obj, right: &Obj) -> Option<(ClosedValuePair, bool)> {
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
        return Some((ClosedValuePair::Radical {
            left_normal: left.to_obj(), right_normal: right.to_obj(),
        }, equal));
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

fn calculate_comparison(
    left: &Obj,
    right: &Obj,
    accepted: &[NumberCompareResult],
) -> Option<ClosedComparisonCalculationProof> {
    let (values, _) = calculate_value_pair(left, right)?;
    let (comparison, left_normal, right_normal) = match values {
        ClosedValuePair::Radical { .. } => return None,
        ClosedValuePair::Decimal { left, right } => {
            (compare_number_strings(&left, &right), left, right)
        }
        ClosedValuePair::Rational { left, right } => (
            left.compare(&right)?,
            left.to_obj().readable_string(),
            right.to_obj().readable_string(),
        ),
        ClosedValuePair::Complex {
            left_real,
            left_imaginary,
            right_real,
            right_imaginary,
        } => {
            if !left_imaginary.is_zero() || !right_imaginary.is_zero() {
                return None;
            }
            (
                left_real.compare(&right_real)?,
                left_real.to_obj().readable_string(),
                right_real.to_obj().readable_string(),
            )
        }
    };
    if !accepted.contains(&comparison) {
        return None;
    }
    Some(ClosedComparisonCalculationProof {
        left_normal,
        right_normal,
        comparison,
    })
}

fn calculate_membership(
    element: &Obj,
    set: &Obj,
    positive: bool,
) -> Option<ClosedMembershipCalculationProof> {
    if let Obj::StandardSet(set) = set {
        let (value, admitted) = calculate_scalar_membership(element, set)?;
        return (admitted == positive).then(|| ClosedMembershipCalculationProof::StandardSet {
            value, set: set.clone(),
        });
    }
    let (start, end, half_open) = match set {
        Obj::SetFormer(SetFormer::ClosedRange(range)) => (&range.start, &range.end, false),
        Obj::SetFormer(SetFormer::Range(range)) => (&range.start, &range.end, true),
        _ => return None,
    };
    let (start, start_integer) = calculate_scalar_membership(start, &StandardSet::Z)?;
    let (end, end_integer) = calculate_scalar_membership(end, &StandardSet::Z)?;
    if !start_integer || !end_integer { return None; }
    let (value, value_integer) = calculate_scalar_membership(element, &StandardSet::Z)?;
    let admitted = if value_integer {
        let value_real = closed_scalar_real(&value)?;
        let lower = value_real.compare(&closed_scalar_real(&start)?)?;
        let upper = value_real.compare(&closed_scalar_real(&end)?)?;
        lower != NumberCompareResult::Less && (upper == NumberCompareResult::Less
            || (!half_open && upper == NumberCompareResult::Equal))
    } else { false };
    (admitted == positive).then(|| ClosedMembershipCalculationProof::IntegerRange {
        value, set: set.clone(), start, end,
    })
}

fn closed_scalar_real(value: &ClosedScalarValue) -> Option<EvalRational> {
    match value {
        ClosedScalarValue::Decimal(normalized_value) => EvalRational::from_obj(
            &Obj::Literal(Literal::Number(Number { normalized_value: normalized_value.clone() })),
        ),
        ClosedScalarValue::ExactComplex { real, imaginary } if imaginary.is_zero() => Some(real.clone()),
        _ => None,
    }
}

fn calculate_scalar_membership(
    element: &Obj,
    set: &StandardSet,
) -> Option<(ClosedScalarValue, bool)> {
    if let Some(number) = calculate_closed_decimal(element) {
        let admitted = normalized_decimal_inhabits_standard_set(&number.normalized_value, set);
        return Some((
            ClosedScalarValue::Decimal(number.normalized_value),
            admitted,
        ));
    }
    let (real, imaginary) = exact_complex_coordinates(element)?;
    let admitted = exact_complex_inhabits_standard_set(&real, &imaginary, set);
    Some((
        ClosedScalarValue::ExactComplex { real, imaginary },
        admitted,
    ))
}

// The general evaluator also handles tuple dimensions and finite-set sizes,
// including trees containing symbolic children. Only its classified numeric
// subset belongs in this closed leaf; keep those structural rules above Direct.
fn calculate_closed_decimal(obj: &Obj) -> Option<Number> {
    if !is_closed_numeric_expr(obj) {
        return None;
    }
    evaluate_obj_to_normalized_decimal_number(obj)
}
