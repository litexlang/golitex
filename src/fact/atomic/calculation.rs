//! Atomic fact argument calculation.

use crate::prelude::*;
impl AtomicFact {
    fn body_vec_after_calculate_each_calculable_arg(original_body: &Vec<Obj>) -> Vec<Obj> {
        let mut next_body = Vec::new();
        for obj in original_body {
            next_body.push(obj.replace_with_numeric_result_if_can_be_calculated().0);
        }
        next_body
    }

    pub fn calculate_args(&self) -> (AtomicFact, bool) {
        let calculated_atomic_fact: AtomicFact = match self {
            AtomicFact::NormalAtomicFact(inner) => NormalAtomicFact::new(
                inner.predicate.clone(),
                Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotNormalAtomicFact(inner) => NotNormalAtomicFact::new(
                inner.predicate.clone(),
                Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::EqualFact(inner) => EqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotEqualFact(inner) => NotEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::LessFact(inner) => LessFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotLessFact(inner) => NotLessFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::GreaterFact(inner) => GreaterFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotGreaterFact(inner) => NotGreaterFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::LessEqualFact(inner) => LessEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotLessEqualFact(inner) => NotLessEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::GreaterEqualFact(inner) => GreaterEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotGreaterEqualFact(inner) => NotGreaterEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsSetFact(inner) => IsSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsSetFact(inner) => NotIsSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsNonemptySetFact(inner) => IsNonemptySetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsNonemptySetFact(inner) => NotIsNonemptySetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsFiniteSetFact(inner) => IsFiniteSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsFiniteSetFact(inner) => NotIsFiniteSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::InFact(inner) => InFact::new(
                inner
                    .element
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotInFact(inner) => NotInFact::new(
                inner
                    .element
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsCartFact(inner) => IsCartFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsCartFact(inner) => NotIsCartFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsTupleFact(inner) => IsTupleFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsTupleFact(inner) => NotIsTupleFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::SubsetFact(inner) => SubsetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotSubsetFact(inner) => NotSubsetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::SupersetFact(inner) => SupersetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotSupersetFact(inner) => NotSupersetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::FnEqualInFact(inner) => FnEqualInFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::FnEqualFact(inner) => FnEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
        };
        let any_argument_replaced = calculated_atomic_fact.to_string() != self.to_string();
        (calculated_atomic_fact, any_argument_replaced)
    }
}
