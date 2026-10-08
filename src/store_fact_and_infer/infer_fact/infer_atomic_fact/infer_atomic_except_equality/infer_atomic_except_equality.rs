use crate::ast::fact::AtomicFact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferBijectiveDefinitionResult, InferBuiltinDefinitionResult,
    InferChoiceFunctionDefinitionResult, InferCoprimeDefinitionResult, InferDvdDefinitionResult,
    InferPrimeDefinitionResult, InferProperSubsetDefinitionResult,
    InferProperSupersetDefinitionResult,
};
use crate::store_fact_and_infer::{
    InferInjectiveDefinitionResult, InferSurjectiveDefinitionResult,
};

impl Runtime {
    // Collect every non-equal atomic infer rule that fires for this fact.
    // Empty Vec means no rule applied (not an error).
    pub(crate) fn infer_atomic_except_equality(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        match atomic_fact {
            AtomicFact::EqualFact(_) => unreachable!(
                "equality facts use infer_equal_fact, not infer_atomic_except_equality"
            ),
            AtomicFact::NormalAtomicFact(normal) => {
                rules.extend(self.infer_normal_atomic_fact_rules(normal, verify_state)?);
            }
            AtomicFact::InFact(in_fact) => {
                rules.extend(self.infer_in_fact_rules(in_fact, verify_state)?);
            }
            AtomicFact::SubsetFact(subset) => {
                if let Some(r) = self.infer_subset_finite_upper_bound(subset, verify_state)? {
                    rules.push(InferAtomicExceptEqualityResult::SubsetFiniteUpperBound(r));
                }
                if let Some(r) = self.infer_subset_elementwise_membership(subset, verify_state)? {
                    rules.push(InferAtomicExceptEqualityResult::SubsetElementwiseMembership(r));
                }
            }
            AtomicFact::SupersetFact(superset) => {
                rules.push(
                    InferAtomicExceptEqualityResult::SupersetElementwiseMembership(
                        self.infer_superset_elementwise_membership(superset, verify_state)?,
                    ),
                );
            }
            // A checked mapping property publishes its quantified definition,
            // as legacy did: surjective(A,B,f) gives every y in B a preimage.
            AtomicFact::InjectiveFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Injective(InferInjectiveDefinitionResult {
                        source_fact_id: f.fact_id,
                        derived,
                    }),
                ));
            }
            AtomicFact::SurjectiveFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Surjective(InferSurjectiveDefinitionResult {
                        source_fact_id: f.fact_id,
                        derived,
                    }),
                ));
            }
            AtomicFact::PrimeFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Prime(InferPrimeDefinitionResult {
                        source_fact_id: f.fact_id,
                        derived,
                    }),
                ));
            }
            AtomicFact::CoprimeFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Coprime(InferCoprimeDefinitionResult {
                        source_fact_id: f.fact_id,
                        derived,
                    }),
                ));
            }
            AtomicFact::ProperSubsetFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::ProperSubset(InferProperSubsetDefinitionResult {
                        source_fact_id: f.fact_id,
                        derived,
                    }),
                ));
            }
            AtomicFact::ProperSupersetFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::ProperSuperset(
                        InferProperSupersetDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived,
                        },
                    ),
                ));
            }
            AtomicFact::DvdFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Dvd(InferDvdDefinitionResult {
                        source_fact_id: f.fact_id,
                        derived,
                    }),
                ));
            }
            AtomicFact::BijectiveFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::Bijective(InferBijectiveDefinitionResult {
                        source_fact_id: f.fact_id,
                        derived,
                    }),
                ));
            }
            // A checked choice certificate releases its defining pointwise
            // membership universal, using the same builder as `by def`.
            AtomicFact::IsChoiceFunctionForFact(f) => {
                let derived =
                    self.store_builtin_definition_consequences(atomic_fact, verify_state)?;
                rules.push(InferAtomicExceptEqualityResult::BuiltinDefinition(
                    InferBuiltinDefinitionResult::ChoiceFunction(
                        InferChoiceFunctionDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived,
                        },
                    ),
                ));
            }
            AtomicFact::LessFact(_) | AtomicFact::GreaterFact(_) => {
                if let Some(r) =
                    self.infer_strict_lower_bound_positive(atomic_fact, verify_state)?
                {
                    rules.push(InferAtomicExceptEqualityResult::StrictLowerBoundPositive(r));
                }
            }
            AtomicFact::LessEqualFact(_) | AtomicFact::GreaterEqualFact(_) => {
                if let Some(r) =
                    self.infer_weak_integer_lower_bound_in_n(atomic_fact, verify_state)?
                {
                    rules.push(InferAtomicExceptEqualityResult::WeakIntegerLowerBoundInN(r));
                }
            }
            AtomicFact::IsSetFact(_)
            | AtomicFact::IsNonemptySetFact(_)
            | AtomicFact::IsFiniteSetFact(_)
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
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
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
    fn store_builtin_definition_consequences(
        &mut self,
        fact: &AtomicFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<crate::store_fact_and_infer::StoreFactAndInferResult>> {
        let mut derived = Vec::new();
        for consequence in self.builtin_atomic_definition_consequences(fact) {
            derived.push(self.store_inferred_fact_and_infer(&consequence, verify_state)?);
        }
        Ok(derived)
    }
}
