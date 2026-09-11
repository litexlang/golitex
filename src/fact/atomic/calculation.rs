//! Atomic fact argument calculation.

use crate::prelude::*;
impl AtomicFact {
    pub fn calculate_args(&self) -> (AtomicFact, bool) {
        self.calculate_args_with_runtime(&Runtime::default())
    }

    fn body_vec_after_calculate_each_calculable_arg(original_body: &Vec<Obj>) -> Vec<Obj> {
        let mut next_body = Vec::new();
        for obj in original_body {
            next_body.push(obj.replace_with_numeric_result_if_can_be_calculated().0);
        }
        next_body
    }

    pub fn calculate_args_with_runtime(&self, runtime: &Runtime) -> (AtomicFact, bool) {
        let calculated_atomic_fact: AtomicFact = match self {
            AtomicFact::NormalAtomicFact(inner) => runtime
                .new_normal_atomic_fact(
                    inner.predicate.clone(),
                    Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::NotNormalAtomicFact(inner) => runtime
                .new_not_normal_atomic_fact(
                    inner.predicate.clone(),
                    Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::EqualFact(inner) => runtime
                .new_equal_fact(
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
            AtomicFact::NotEqualFact(inner) => runtime
                .new_not_equal_fact(
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
            AtomicFact::LessFact(inner) => runtime
                .new_less_fact(
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
            AtomicFact::NotLessFact(inner) => runtime
                .new_not_less_fact(
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
            AtomicFact::GreaterFact(inner) => runtime
                .new_greater_fact(
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
            AtomicFact::NotGreaterFact(inner) => runtime
                .new_not_greater_fact(
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
            AtomicFact::LessEqualFact(inner) => runtime
                .new_less_equal_fact(
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
            AtomicFact::NotLessEqualFact(inner) => runtime
                .new_not_less_equal_fact(
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
            AtomicFact::GreaterEqualFact(inner) => runtime
                .new_greater_equal_fact(
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
            AtomicFact::NotGreaterEqualFact(inner) => runtime
                .new_not_greater_equal_fact(
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
            AtomicFact::IsSetFact(inner) => runtime
                .new_is_set_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::NotIsSetFact(inner) => runtime
                .new_not_is_set_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::IsNonemptySetFact(inner) => runtime
                .new_is_nonempty_set_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::NotIsNonemptySetFact(inner) => runtime
                .new_not_is_nonempty_set_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::IsFiniteSetFact(inner) => runtime
                .new_is_finite_set_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::NotIsFiniteSetFact(inner) => runtime
                .new_not_is_finite_set_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::InFact(inner) => runtime
                .new_in_fact(
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
            AtomicFact::NotInFact(inner) => runtime
                .new_not_in_fact(
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
            AtomicFact::IsCartFact(inner) => runtime
                .new_is_cart_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::NotIsCartFact(inner) => runtime
                .new_not_is_cart_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::IsTupleFact(inner) => runtime
                .new_is_tuple_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::NotIsTupleFact(inner) => runtime
                .new_not_is_tuple_fact(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                )
                .into(),
            AtomicFact::SubsetFact(inner) => runtime
                .new_subset_fact(
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
            AtomicFact::NotSubsetFact(inner) => runtime
                .new_not_subset_fact(
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
            AtomicFact::SupersetFact(inner) => runtime
                .new_superset_fact(
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
            AtomicFact::NotSupersetFact(inner) => runtime
                .new_not_superset_fact(
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
            AtomicFact::FnEqualInFact(inner) => runtime
                .new_fn_equal_in_fact(
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
            AtomicFact::FnEqualFact(inner) => runtime
                .new_fn_equal_fact(
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
