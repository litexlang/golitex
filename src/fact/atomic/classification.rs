//! Atomic fact polarity, keys, and argument reordering.

use crate::prelude::*;

#[cfg(test)]
#[path = "../../../tests/unit/fact/atomic/polarity.rs"]
mod tests;
impl AtomicFact {
    pub fn transposed_binary_order_equivalent(&self) -> Option<Self> {
        self.transposed_binary_order_equivalent_with_runtime(&Runtime::default())
    }

    pub fn symmetric_reordered_args(&self, gather: &[usize]) -> Option<Self> {
        self.symmetric_reordered_args_with_runtime(&Runtime::default(), gather)
    }

    fn predicate_string(&self) -> String {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.predicate.to_string(),
            AtomicFact::EqualFact(_) => EQUAL.to_string(),
            AtomicFact::LessFact(_) => LESS.to_string(),
            AtomicFact::GreaterFact(_) => GREATER.to_string(),
            AtomicFact::LessEqualFact(_) => LESS_EQUAL.to_string(),
            AtomicFact::GreaterEqualFact(_) => GREATER_EQUAL.to_string(),
            AtomicFact::IsSetFact(_) => IS_SET.to_string(),
            AtomicFact::IsNonemptySetFact(_) => IS_NONEMPTY_SET.to_string(),
            AtomicFact::IsFiniteSetFact(_) => IS_FINITE_SET.to_string(),
            AtomicFact::InFact(_) => IN.to_string(),
            AtomicFact::IsCartFact(_) => IS_CART.to_string(),
            AtomicFact::IsTupleFact(_) => IS_TUPLE.to_string(),
            AtomicFact::SubsetFact(_) => SUBSET.to_string(),
            AtomicFact::SupersetFact(_) => SUPERSET.to_string(),
            AtomicFact::NotNormalAtomicFact(x) => x.predicate.to_string(),
            AtomicFact::NotEqualFact(_) => EQUAL.to_string(),
            AtomicFact::NotLessFact(_) => LESS.to_string(),
            AtomicFact::NotGreaterFact(_) => GREATER.to_string(),
            AtomicFact::NotLessEqualFact(_) => LESS_EQUAL.to_string(),
            AtomicFact::NotGreaterEqualFact(_) => GREATER_EQUAL.to_string(),
            AtomicFact::NotIsSetFact(_) => IS_SET.to_string(),
            AtomicFact::NotIsNonemptySetFact(_) => IS_NONEMPTY_SET.to_string(),
            AtomicFact::NotIsFiniteSetFact(_) => IS_FINITE_SET.to_string(),
            AtomicFact::NotInFact(_) => IN.to_string(),
            AtomicFact::NotIsCartFact(_) => IS_CART.to_string(),
            AtomicFact::NotIsTupleFact(_) => IS_TUPLE.to_string(),
            AtomicFact::NotSubsetFact(_) => SUBSET.to_string(),
            AtomicFact::NotSupersetFact(_) => SUPERSET.to_string(),
            AtomicFact::FnEqualFact(_) => FN_EQ.to_string(),
        }
    }

    pub fn has_positive_polarity(&self) -> bool {
        match self {
            AtomicFact::NormalAtomicFact(_) => true,
            AtomicFact::EqualFact(_) => true,
            AtomicFact::LessFact(_) => true,
            AtomicFact::GreaterFact(_) => true,
            AtomicFact::LessEqualFact(_) => true,
            AtomicFact::GreaterEqualFact(_) => true,
            AtomicFact::IsSetFact(_) => true,
            AtomicFact::IsNonemptySetFact(_) => true,
            AtomicFact::IsFiniteSetFact(_) => true,
            AtomicFact::InFact(_) => true,
            AtomicFact::IsCartFact(_) => true,
            AtomicFact::IsTupleFact(_) => true,
            AtomicFact::SubsetFact(_) => true,
            AtomicFact::SupersetFact(_) => true,
            AtomicFact::NotNormalAtomicFact(_) => false,
            AtomicFact::NotEqualFact(_) => false,
            AtomicFact::NotLessFact(_) => false,
            AtomicFact::NotGreaterFact(_) => false,
            AtomicFact::NotLessEqualFact(_) => false,
            AtomicFact::NotGreaterEqualFact(_) => false,
            AtomicFact::NotIsSetFact(_) => false,
            AtomicFact::NotIsNonemptySetFact(_) => false,
            AtomicFact::NotIsFiniteSetFact(_) => false,
            AtomicFact::NotInFact(_) => false,
            AtomicFact::NotIsCartFact(_) => false,
            AtomicFact::NotIsTupleFact(_) => false,
            AtomicFact::NotSubsetFact(_) => false,
            AtomicFact::NotSupersetFact(_) => false,
            AtomicFact::FnEqualFact(_) => true,
        }
    }

    pub fn key(&self) -> String {
        return self.predicate_string();
    }

    pub fn transposed_binary_order_equivalent_with_runtime(
        &self,
        runtime: &Runtime,
    ) -> Option<Self> {
        match self {
            AtomicFact::NormalAtomicFact(f)
                if f.body.len() == 2
                    && matches!(
                        f.predicate.to_string().as_str(),
                        PROPER_SUBSET | PROPER_SUPERSET
                    ) =>
            {
                let transposed_predicate = if f.predicate.to_string() == PROPER_SUBSET {
                    PROPER_SUPERSET
                } else {
                    PROPER_SUBSET
                };
                Some(
                    runtime
                        .new_normal_atomic_fact(
                            AtomicName::WithoutMod(transposed_predicate.to_string()),
                            vec![f.body[1].clone(), f.body[0].clone()],
                            f.line_file.clone(),
                        )
                        .into(),
                )
            }
            AtomicFact::NotNormalAtomicFact(f)
                if f.body.len() == 2
                    && matches!(
                        f.predicate.to_string().as_str(),
                        PROPER_SUBSET | PROPER_SUPERSET
                    ) =>
            {
                let transposed_predicate = if f.predicate.to_string() == PROPER_SUBSET {
                    PROPER_SUPERSET
                } else {
                    PROPER_SUBSET
                };
                Some(
                    runtime
                        .new_not_normal_atomic_fact(
                            AtomicName::WithoutMod(transposed_predicate.to_string()),
                            vec![f.body[1].clone(), f.body[0].clone()],
                            f.line_file.clone(),
                        )
                        .into(),
                )
            }
            AtomicFact::LessFact(f) => Some(
                runtime
                    .new_greater_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                    .into(),
            ),
            AtomicFact::GreaterFact(f) => Some(
                runtime
                    .new_less_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                    .into(),
            ),
            AtomicFact::LessEqualFact(f) => Some(AtomicFact::GreaterEqualFact(
                runtime.new_greater_equal_fact(
                    f.right.clone(),
                    f.left.clone(),
                    f.line_file.clone(),
                ),
            )),
            AtomicFact::GreaterEqualFact(f) => Some(
                runtime
                    .new_less_equal_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                    .into(),
            ),
            AtomicFact::NotLessFact(f) => Some(
                runtime
                    .new_not_greater_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                    .into(),
            ),
            AtomicFact::NotGreaterFact(f) => Some(
                runtime
                    .new_not_less_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                    .into(),
            ),
            AtomicFact::NotLessEqualFact(f) => Some(AtomicFact::NotGreaterEqualFact(
                runtime.new_not_greater_equal_fact(
                    f.right.clone(),
                    f.left.clone(),
                    f.line_file.clone(),
                ),
            )),
            AtomicFact::NotGreaterEqualFact(f) => Some(AtomicFact::NotLessEqualFact(
                runtime.new_not_less_equal_fact(
                    f.right.clone(),
                    f.left.clone(),
                    f.line_file.clone(),
                ),
            )),
            AtomicFact::FnEqualFact(f) => Some(
                runtime
                    .new_fn_equal_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                    .into(),
            ),
            _ => None,
        }
    }

    pub fn symmetric_reordered_args_with_runtime(
        &self,
        runtime: &Runtime,
        gather: &[usize],
    ) -> Option<Self> {
        match self {
            AtomicFact::NormalAtomicFact(f) => {
                let n = f.body.len();
                if gather.len() != n || n < 2 {
                    return None;
                }
                let mut seen = vec![false; n];
                for &i in gather {
                    if i >= n || seen[i] {
                        return None;
                    }
                    seen[i] = true;
                }
                let new_body: Vec<Obj> = gather.iter().map(|&i| f.body[i].clone()).collect();
                Some(
                    runtime
                        .new_normal_atomic_fact(f.predicate.clone(), new_body, f.line_file.clone())
                        .into(),
                )
            }
            _ => None,
        }
    }
}
