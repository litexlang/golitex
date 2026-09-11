//! Atomic fact logical negation.

use crate::prelude::*;
impl AtomicFact {
    pub fn logical_negation(&self) -> Result<AtomicFact, RuntimeError> {
        self.logical_negation_with_runtime(&Runtime::default())
    }

    /// Return the logical negation of an atomic fact.
    ///
    /// Function equality has no negated atomic form in Litex. Swapping its two
    /// sides is symmetry, not negation, so callers must handle that case.
    pub fn logical_negation_with_runtime(
        &self,
        runtime: &Runtime,
    ) -> Result<AtomicFact, RuntimeError> {
        if matches!(
            self,
            AtomicFact::FnEqualInFact(_) | AtomicFact::FnEqualFact(_)
        ) {
            return Err(RuntimeError::from(NewFactRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("logical negation is not supported for `{}`", self),
                    self.line_file(),
                ),
            )));
        }

        Ok(match self {
            AtomicFact::NormalAtomicFact(a) => {
                AtomicFact::NotNormalAtomicFact(runtime.new_not_normal_atomic_fact(
                    a.predicate.clone(),
                    a.body.clone(),
                    a.line_file.clone(),
                ))
            }
            AtomicFact::NotNormalAtomicFact(a) => {
                AtomicFact::NormalAtomicFact(runtime.new_normal_atomic_fact(
                    a.predicate.clone(),
                    a.body.clone(),
                    a.line_file.clone(),
                ))
            }
            AtomicFact::EqualFact(a) => runtime
                .new_not_equal_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::LessFact(a) => runtime
                .new_not_less_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::GreaterFact(a) => runtime
                .new_not_greater_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::LessEqualFact(a) => runtime
                .new_not_less_equal_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::GreaterEqualFact(a) => {
                AtomicFact::NotGreaterEqualFact(runtime.new_not_greater_equal_fact(
                    a.left.clone(),
                    a.right.clone(),
                    a.line_file.clone(),
                ))
            }
            AtomicFact::IsSetFact(a) => runtime
                .new_not_is_set_fact(a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::IsNonemptySetFact(a) => AtomicFact::NotIsNonemptySetFact(
                runtime.new_not_is_nonempty_set_fact(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::IsFiniteSetFact(a) => AtomicFact::NotIsFiniteSetFact(
                runtime.new_not_is_finite_set_fact(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::InFact(a) => runtime
                .new_not_in_fact(a.element.clone(), a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::IsCartFact(a) => runtime
                .new_not_is_cart_fact(a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::IsTupleFact(a) => runtime
                .new_not_is_tuple_fact(a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::SubsetFact(a) => runtime
                .new_not_subset_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::SupersetFact(a) => runtime
                .new_not_superset_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotEqualFact(a) => runtime
                .new_equal_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotLessFact(a) => runtime
                .new_less_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotGreaterFact(a) => runtime
                .new_greater_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotLessEqualFact(a) => runtime
                .new_less_equal_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotGreaterEqualFact(a) => {
                AtomicFact::GreaterEqualFact(runtime.new_greater_equal_fact(
                    a.left.clone(),
                    a.right.clone(),
                    a.line_file.clone(),
                ))
            }
            AtomicFact::NotIsSetFact(a) => runtime
                .new_is_set_fact(a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotIsNonemptySetFact(a) => AtomicFact::IsNonemptySetFact(
                runtime.new_is_nonempty_set_fact(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotIsFiniteSetFact(a) => runtime
                .new_is_finite_set_fact(a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotInFact(a) => runtime
                .new_in_fact(a.element.clone(), a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotIsCartFact(a) => runtime
                .new_is_cart_fact(a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotIsTupleFact(a) => runtime
                .new_is_tuple_fact(a.set.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotSubsetFact(a) => runtime
                .new_subset_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::NotSupersetFact(a) => runtime
                .new_superset_fact(a.left.clone(), a.right.clone(), a.line_file.clone())
                .into(),
            AtomicFact::FnEqualInFact(_) | AtomicFact::FnEqualFact(_) => {
                unreachable!("function equality is handled before logical negation")
            }
        })
    }
}
