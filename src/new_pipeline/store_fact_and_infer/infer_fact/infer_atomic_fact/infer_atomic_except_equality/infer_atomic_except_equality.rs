use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferAtomicExceptEqualityResult;

impl Runtime {
    // Collect every non-equal atomic infer rule that fires for this fact.
    // Empty Vec means no rule applied (not an error).
    pub(crate) fn infer_atomic_except_equality(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        match atomic_fact {
            AtomicFact::EqualFact(_) => unreachable!(
                "equality facts use infer_equal_fact, not infer_atomic_except_equality"
            ),
            AtomicFact::NormalAtomicFact(normal) => {
                rules.extend(self.infer_normal_atomic_fact_rules(normal)?);
            }
            AtomicFact::InFact(in_fact) => {
                rules.extend(self.infer_in_fact_rules(in_fact)?);
            }
            AtomicFact::IsCartFact(is_cart) => {
                rules.push(InferAtomicExceptEqualityResult::IsCartDimensionLowerBound(
                    self.infer_is_cart_dimension_lower_bound(is_cart)?,
                ));
            }
            AtomicFact::SubsetFact(subset) => {
                if let Some(r) = self.infer_subset_elementwise_membership(subset)? {
                    rules.push(InferAtomicExceptEqualityResult::SubsetElementwiseMembership(r));
                }
            }
            AtomicFact::SupersetFact(superset) => {
                rules.push(
                    InferAtomicExceptEqualityResult::SupersetElementwiseMembership(
                        self.infer_superset_elementwise_membership(superset)?,
                    ),
                );
            }
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_)
            | AtomicFact::IsSetFact(_)
            | AtomicFact::IsNonemptySetFact(_)
            | AtomicFact::IsFiniteSetFact(_)
            | AtomicFact::IsTupleFact(_)
            | AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::NotEqualFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::NotIsCartFact(_)
            | AtomicFact::NotIsTupleFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_) => {}
        }
        Ok(rules)
    }
}
