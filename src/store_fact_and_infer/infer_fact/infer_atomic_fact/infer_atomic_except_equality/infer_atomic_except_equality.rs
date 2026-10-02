use crate::ast::fact::AtomicFact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{InferAtomicExceptEqualityResult, InferBuiltinDefinitionResult};

impl Runtime {
    // Collect every non-equal atomic infer rule that fires for this fact.
    // Empty Vec means no rule applied (not an error).
    pub(crate) fn infer_atomic_except_equality(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        let consequences = self.builtin_atomic_definition_consequences(atomic_fact);
        if !consequences.is_empty() {
            let mut derived = Vec::new();
            for fact in consequences {
                derived.push(self.store_inferred_fact_and_infer(&fact)?);
            }
            rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                InferBuiltinDefinitionResult { source_fact_id: atomic_fact.fact_id(), derived },
            ));
        }

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
            | AtomicFact::NotSupersetFact(_)
            | AtomicFact::ProperSubsetFact(_)
            | AtomicFact::ProperSupersetFact(_)
            | AtomicFact::PrimeFact(_)
            | AtomicFact::CoprimeFact(_)
            | AtomicFact::DvdFact(_)
            | AtomicFact::InjectiveFact(_)
            | AtomicFact::SurjectiveFact(_)
            | AtomicFact::BijectiveFact(_)
            | AtomicFact::IsChoiceFunctionForFact(_)
            | AtomicFact::NotProperSubsetFact(_)
            | AtomicFact::NotProperSupersetFact(_)
            | AtomicFact::NotPrimeFact(_)
            | AtomicFact::NotCoprimeFact(_)
            | AtomicFact::NotDvdFact(_)
            | AtomicFact::NotInjectiveFact(_)
            | AtomicFact::NotSurjectiveFact(_)
            | AtomicFact::NotBijectiveFact(_)
            | AtomicFact::NotIsChoiceFunctionForFact(_) => {}
        }
        Ok(rules)
    }
}
