use crate::ast::fact::AtomicFact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{InferAtomicExceptEqualityResult, InferBuiltinDefinitionResult, InferPrimeDefinitionResult, InferCoprimeDefinitionResult, InferProperSubsetDefinitionResult, InferProperSupersetDefinitionResult, InferDvdDefinitionResult, InferBijectiveDefinitionResult, InferChoiceFunctionDefinitionResult};

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
            AtomicFact::PrimeFact(f) => {
                let derived = self.store_builtin_definition_consequences(atomic_fact)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Prime(InferPrimeDefinitionResult { source_fact_id: f.fact_id, derived }),
                ));
            }
            AtomicFact::CoprimeFact(f) => {
                let derived = self.store_builtin_definition_consequences(atomic_fact)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Coprime(InferCoprimeDefinitionResult { source_fact_id: f.fact_id, derived }),
                ));
            }
            AtomicFact::ProperSubsetFact(f) => {
                let derived = self.store_builtin_definition_consequences(atomic_fact)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::ProperSubset(InferProperSubsetDefinitionResult { source_fact_id: f.fact_id, derived }),
                ));
            }
            AtomicFact::ProperSupersetFact(f) => {
                let derived = self.store_builtin_definition_consequences(atomic_fact)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::ProperSuperset(InferProperSupersetDefinitionResult { source_fact_id: f.fact_id, derived }),
                ));
            }
            AtomicFact::DvdFact(f) => {
                let derived = self.store_builtin_definition_consequences(atomic_fact)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Dvd(InferDvdDefinitionResult { source_fact_id: f.fact_id, derived }),
                ));
            }
            AtomicFact::BijectiveFact(f) => {
                let derived = self.store_builtin_definition_consequences(atomic_fact)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Bijective(InferBijectiveDefinitionResult { source_fact_id: f.fact_id, derived }),
                ));
            }
            // A checked choice certificate releases its defining pointwise
            // membership universal, using the same builder as `by def`.
            AtomicFact::IsChoiceFunctionForFact(f) => {
                let derived=self.store_builtin_definition_consequences(atomic_fact)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::ChoiceFunction(InferChoiceFunctionDefinitionResult {source_fact_id:f.fact_id,derived}),
                ));
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
            | AtomicFact::InjectiveFact(_)
            | AtomicFact::SurjectiveFact(_)
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
    fn store_builtin_definition_consequences(&mut self, fact: &AtomicFact)
        -> RuntimeResult<Vec<crate::store_fact_and_infer::StoreFactAndInferResult>> {
        let mut derived=Vec::new();
        for consequence in self.builtin_atomic_definition_consequences(fact) {
            derived.push(self.store_inferred_fact_and_infer(&consequence)?);
        }
        Ok(derived)
    }

}
