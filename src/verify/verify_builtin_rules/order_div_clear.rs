use crate::prelude::*;
use super::number_compare::{compare_normalized_number_str_to_zero, NumberCompareResult};

fn evaluated_numeric_denominator_sign_positive(den: &Obj) -> Option<bool> {
    let n = den.evaluate_to_normalized_decimal_number()?;
    match compare_normalized_number_str_to_zero(&n.normalized_value) {
        NumberCompareResult::Equal => None,
        NumberCompareResult::Greater => Some(true),
        NumberCompareResult::Less => Some(false),
    }
}

#[derive(Clone, Copy)]
enum OrderRelationForDivClear {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl OrderRelationForDivClear {
    fn flip(self) -> Self {
        match self {
            Self::Less => Self::Greater,
            Self::LessEqual => Self::GreaterEqual,
            Self::Greater => Self::Less,
            Self::GreaterEqual => Self::LessEqual,
        }
    }

    fn after_multiply_by_signed_denominator(self, denominator_is_positive: bool) -> Self {
        if denominator_is_positive {
            self
        } else {
            self.flip()
        }
    }

    fn to_atomic_fact(self, left: Obj, right: Obj, line_file: LineFile) -> AtomicFact {
        match self {
            Self::Less => AtomicFact::LessFact(LessFact::new(left, right, line_file)),
            Self::LessEqual => {
                AtomicFact::LessEqualFact(LessEqualFact::new(left, right, line_file))
            }
            Self::Greater => AtomicFact::LessFact(LessFact::new(right, left, line_file)),
            Self::GreaterEqual => {
                AtomicFact::LessEqualFact(LessEqualFact::new(right, left, line_file))
            }
        }
    }
}

fn order_relation_and_operands(
    atomic_fact: &AtomicFact,
) -> Option<(OrderRelationForDivClear, Obj, Obj, LineFile)> {
    match atomic_fact {
        AtomicFact::LessFact(f) => Some((
            OrderRelationForDivClear::Less,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        AtomicFact::LessEqualFact(f) => Some((
            OrderRelationForDivClear::LessEqual,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        AtomicFact::GreaterFact(f) => Some((
            OrderRelationForDivClear::Greater,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        AtomicFact::GreaterEqualFact(f) => Some((
            OrderRelationForDivClear::GreaterEqual,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        _ => None,
    }
}

pub(crate) fn try_build_order_fact_after_clearing_numeric_div_denominators(
    atomic_fact: &AtomicFact,
) -> Option<AtomicFact> {
    let (rel, left, right, line_file) = order_relation_and_operands(atomic_fact)?;

    if let (Obj::Div(ld), Obj::Div(rd)) = (&left, &right) {
        let left_den_pos = evaluated_numeric_denominator_sign_positive(ld.right.as_ref())?;
        let right_den_pos = evaluated_numeric_denominator_sign_positive(rd.right.as_ref())?;
        let product_positive = left_den_pos == right_den_pos;
        let rel2 = rel.after_multiply_by_signed_denominator(product_positive);
        let new_left = Obj::Mul(Mul::new(
            (*ld.left).clone(),
            (*rd.right).clone(),
        ));
        let new_right = Obj::Mul(Mul::new(
            (*ld.right).clone(),
            (*rd.left).clone(),
        ));
        return Some(rel2.to_atomic_fact(new_left, new_right, line_file));
    }

    if let Obj::Div(ld) = &left {
        if !matches!(&right, Obj::Div(_)) {
            let den_pos = evaluated_numeric_denominator_sign_positive(ld.right.as_ref())?;
            let rel2 = rel.after_multiply_by_signed_denominator(den_pos);
            let new_left = (*ld.left).clone();
            let new_right = Obj::Mul(Mul::new((*ld.right).clone(), right.clone()));
            return Some(rel2.to_atomic_fact(new_left, new_right, line_file));
        }
    }

    if let Obj::Div(rd) = &right {
        if !matches!(&left, Obj::Div(_)) {
            let den_pos = evaluated_numeric_denominator_sign_positive(rd.right.as_ref())?;
            let rel2 = rel.after_multiply_by_signed_denominator(den_pos);
            let new_left = Obj::Mul(Mul::new((*rd.right).clone(), left.clone()));
            let new_right = (*rd.left).clone();
            return Some(rel2.to_atomic_fact(new_left, new_right, line_file));
        }
    }

    None
}
