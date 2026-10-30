use crate::prelude::*;
use crate::store_fact_and_infer::*;

impl Runtime {
    pub(crate) fn infer_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<InferAtomicFactResult> {
        match fact {
            AtomicFact::MultivariableAnalysisFact(f) => {
                Ok(InferAtomicFactResult::MultivariableAnalysisFact(vec![
                    InferMultivariableAnalysisFactResult::Definition(
                        InferMultivariableAnalysisDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_multivariable_definition(f, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotMultivariableAnalysisFact(_) => Ok(
                InferAtomicFactResult::NotMultivariableAnalysisFact(Vec::new()),
            ),
            AtomicFact::HasRiemannIntegralFact(f) => {
                Ok(InferAtomicFactResult::HasRiemannIntegralFact(vec![
                    InferHasRiemannIntegralFactResult::Definition(
                        InferHasRiemannIntegralDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_real_analysis_definition(fact, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotHasRiemannIntegralFact(_) => {
                Ok(InferAtomicFactResult::NotHasRiemannIntegralFact(Vec::new()))
            }
            AtomicFact::FunctionRiemannIntegrableFact(f) => {
                Ok(InferAtomicFactResult::FunctionRiemannIntegrableFact(vec![
                    InferFunctionRiemannIntegrableFactResult::Definition(
                        InferFunctionRiemannIntegrableDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_real_analysis_definition(fact, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotFunctionRiemannIntegrableFact(_) => Ok(
                InferAtomicFactResult::NotFunctionRiemannIntegrableFact(Vec::new()),
            ),
            AtomicFact::HasDerivativeAtFact(f) => {
                let function_domain =
                    self.checked_real_function_limit_domain(&f.function, state)?;
                let mut derived = Vec::new();
                if let Some(domain) = &function_domain {
                    for clause in self.derivative_clauses_in_domain(f, domain) {
                        derived.push(self.store_inferred_fact(&clause)?);
                    }
                }
                let existence = self.derivative_existence(f.function.clone(), f.point.clone());
                derived.push(self.store_inferred_fact(&existence)?);
                let differentiable: Fact = FunctionDifferentiableAtFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    function: f.function.clone(),
                    point: f.point.clone(),
                    line_file: None,
                }
                .into();
                derived.push(self.store_inferred_fact(&differentiable)?);
                Ok(InferAtomicFactResult::HasDerivativeAtFact(vec![
                    InferHasDerivativeAtFactResult::Definition(
                        InferHasDerivativeAtDefinitionResult {
                            source_fact_id: f.fact_id,
                            function_domain,
                            derived,
                        },
                    ),
                ]))
            }
            AtomicFact::NotHasDerivativeAtFact(_) => {
                Ok(InferAtomicFactResult::NotHasDerivativeAtFact(Vec::new()))
            }
            AtomicFact::FunctionDifferentiableAtFact(f) => {
                let existence_fact = self.derivative_existence(f.function.clone(), f.point.clone());
                let existence = self.store_inferred_fact(&existence_fact)?;
                let function_domain =
                    self.checked_real_function_limit_domain(&f.function, state)?;
                let interior = if let Some(domain) = &function_domain {
                    let fact =
                        self.derivative_interior_condition(domain.domain.clone(), f.point.clone());
                    Some(self.store_inferred_fact(&fact)?)
                } else {
                    None
                };
                Ok(InferAtomicFactResult::FunctionDifferentiableAtFact(vec![
                    InferFunctionDifferentiableAtFactResult::Definition(
                        InferFunctionDifferentiableAtDefinitionResult {
                            source_fact_id: f.fact_id,
                            existence,
                            function_domain,
                            interior,
                        },
                    ),
                ]))
            }
            AtomicFact::NotFunctionDifferentiableAtFact(_) => Ok(
                InferAtomicFactResult::NotFunctionDifferentiableAtFact(Vec::new()),
            ),
            AtomicFact::RealSetBoundFact(f) => Ok(InferAtomicFactResult::RealSetBoundFact(vec![
                InferRealSetBoundFactResult::Definition(InferRealSetBoundDefinitionResult {
                    source_fact_id: f.fact_id,
                    derived: self.store_real_analysis_definition(fact, state)?,
                }),
            ])),
            AtomicFact::NotRealSetBoundFact(_) => {
                Ok(InferAtomicFactResult::NotRealSetBoundFact(Vec::new()))
            }
            AtomicFact::RealSetBoundedFact(f) => {
                Ok(InferAtomicFactResult::RealSetBoundedFact(vec![
                    InferRealSetBoundedFactResult::Definition(
                        InferRealSetBoundedDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_real_analysis_definition(fact, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotRealSetBoundedFact(_) => {
                Ok(InferAtomicFactResult::NotRealSetBoundedFact(Vec::new()))
            }
            AtomicFact::SequenceAnalysisFact(f) => {
                Ok(InferAtomicFactResult::SequenceAnalysisFact(vec![
                    InferSequenceAnalysisFactResult::Definition(
                        InferSequenceAnalysisDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_real_analysis_definition(fact, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotSequenceAnalysisFact(_) => {
                Ok(InferAtomicFactResult::NotSequenceAnalysisFact(Vec::new()))
            }
            AtomicFact::RealAccumulationFact(f) => {
                Ok(InferAtomicFactResult::RealAccumulationFact(vec![
                    InferRealAccumulationFactResult::Definition(
                        InferRealAccumulationDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_real_analysis_definition(fact, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotRealAccumulationFact(_) => {
                Ok(InferAtomicFactResult::NotRealAccumulationFact(Vec::new()))
            }
            AtomicFact::FunctionContinuousAtFact(f) => {
                let Some(function_domain) =
                    self.checked_real_function_limit_domain(&f.function, state)?
                else {
                    return Ok(InferAtomicFactResult::FunctionContinuousAtFact(Vec::new()));
                };
                let clause = self.continuity_epsilon(
                    f.function.clone(),
                    function_domain.domain.clone(),
                    f.point.clone(),
                    f.side,
                );
                let derived = vec![self.store_inferred_fact(&clause)?];
                Ok(InferAtomicFactResult::FunctionContinuousAtFact(vec![
                    InferFunctionContinuousAtFactResult::Definition(
                        InferFunctionContinuousAtDefinitionResult {
                            source_fact_id: f.fact_id,
                            function_domain,
                            derived,
                        },
                    ),
                ]))
            }
            AtomicFact::NotFunctionContinuousAtFact(_) => Ok(
                InferAtomicFactResult::NotFunctionContinuousAtFact(Vec::new()),
            ),
            AtomicFact::FunctionContinuousFact(f) => {
                Ok(InferAtomicFactResult::FunctionContinuousFact(vec![
                    InferFunctionContinuousFactResult::Definition(
                        InferFunctionContinuousDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_real_analysis_definition(fact, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotFunctionContinuousFact(_) => {
                Ok(InferAtomicFactResult::NotFunctionContinuousFact(Vec::new()))
            }
            AtomicFact::FunctionLipschitzFact(f) => {
                Ok(InferAtomicFactResult::FunctionLipschitzFact(vec![
                    InferFunctionLipschitzFactResult::Definition(
                        InferFunctionLipschitzDefinitionResult {
                            source_fact_id: f.fact_id,
                            derived: self.store_real_analysis_definition(fact, state)?,
                        },
                    ),
                ]))
            }
            AtomicFact::NotFunctionLipschitzFact(_) => {
                Ok(InferAtomicFactResult::NotFunctionLipschitzFact(Vec::new()))
            }
            AtomicFact::HasFunctionLimitFact(_) => {
                Ok(InferAtomicFactResult::HasFunctionLimitFact(Vec::new()))
            }
            AtomicFact::HasSequenceLimitFact(_) => {
                Ok(InferAtomicFactResult::HasSequenceLimitFact(Vec::new()))
            }
            AtomicFact::HasSequenceLimsupFact(_) => {
                Ok(InferAtomicFactResult::HasSequenceLimsupFact(Vec::new()))
            }
            AtomicFact::HasSequenceLiminfFact(_) => {
                Ok(InferAtomicFactResult::HasSequenceLiminfFact(Vec::new()))
            }
            AtomicFact::NotHasFunctionLimitFact(_) => {
                Ok(InferAtomicFactResult::NotHasFunctionLimitFact(Vec::new()))
            }
            AtomicFact::NotHasSequenceLimitFact(_) => {
                Ok(InferAtomicFactResult::NotHasSequenceLimitFact(Vec::new()))
            }
            AtomicFact::NotHasSequenceLimsupFact(_) => {
                Ok(InferAtomicFactResult::NotHasSequenceLimsupFact(Vec::new()))
            }
            AtomicFact::NotHasSequenceLiminfFact(_) => {
                Ok(InferAtomicFactResult::NotHasSequenceLiminfFact(Vec::new()))
            }
            AtomicFact::NormalAtomicFact(f) => Ok(InferAtomicFactResult::NormalAtomicFact(
                self.infer_normal_atomic_fact(f, state)?,
            )),
            AtomicFact::EqualFact(f) => Ok(InferAtomicFactResult::EqualFact(
                self.infer_equal_fact(f, state)?,
            )),
            AtomicFact::LessFact(f) => Ok(InferAtomicFactResult::LessFact(
                self.infer_less_fact(f, state)?,
            )),
            AtomicFact::GreaterFact(f) => Ok(InferAtomicFactResult::GreaterFact(
                self.infer_greater_fact(f, state)?,
            )),
            AtomicFact::LessEqualFact(f) => Ok(InferAtomicFactResult::LessEqualFact(
                self.infer_less_equal_fact(f, state)?,
            )),
            AtomicFact::GreaterEqualFact(f) => Ok(InferAtomicFactResult::GreaterEqualFact(
                self.infer_greater_equal_fact(f, state)?,
            )),
            AtomicFact::IsSetFact(_) => Ok(InferAtomicFactResult::IsSetFact(Vec::new())),
            AtomicFact::IsNonemptySetFact(_) => {
                Ok(InferAtomicFactResult::IsNonemptySetFact(Vec::new()))
            }
            AtomicFact::IsFiniteSetFact(_) => {
                Ok(InferAtomicFactResult::IsFiniteSetFact(Vec::new()))
            }
            AtomicFact::InFact(f) => {
                Ok(InferAtomicFactResult::InFact(self.infer_in_fact(f, state)?))
            }
            AtomicFact::SubsetFact(f) => Ok(InferAtomicFactResult::SubsetFact(
                self.infer_subset_fact(f, state)?,
            )),
            AtomicFact::SupersetFact(f) => Ok(InferAtomicFactResult::SupersetFact(
                self.infer_superset_fact(f, state)?,
            )),
            AtomicFact::ProperSubsetFact(f) => Ok(InferAtomicFactResult::ProperSubsetFact(
                self.infer_proper_subset_fact(f, state)?,
            )),
            AtomicFact::ProperSupersetFact(f) => Ok(InferAtomicFactResult::ProperSupersetFact(
                self.infer_proper_superset_fact(f, state)?,
            )),
            AtomicFact::PrimeFact(f) => Ok(InferAtomicFactResult::PrimeFact(
                self.infer_prime_fact(f, state)?,
            )),
            AtomicFact::CoprimeFact(f) => Ok(InferAtomicFactResult::CoprimeFact(
                self.infer_coprime_fact(f, state)?,
            )),
            AtomicFact::DvdFact(f) => Ok(InferAtomicFactResult::DvdFact(
                self.infer_dvd_fact(f, state)?,
            )),
            AtomicFact::InjectiveFact(f) => Ok(InferAtomicFactResult::InjectiveFact(
                self.infer_injective_fact(f, state)?,
            )),
            AtomicFact::SurjectiveFact(f) => Ok(InferAtomicFactResult::SurjectiveFact(
                self.infer_surjective_fact(f, state)?,
            )),
            AtomicFact::BijectiveFact(f) => Ok(InferAtomicFactResult::BijectiveFact(
                self.infer_bijective_fact(f, state)?,
            )),
            AtomicFact::IsChoiceFunctionForFact(f) => {
                Ok(InferAtomicFactResult::IsChoiceFunctionForFact(
                    self.infer_is_choice_function_for_fact(f, state)?,
                ))
            }
            AtomicFact::NotNormalAtomicFact(_) => {
                Ok(InferAtomicFactResult::NotNormalAtomicFact(Vec::new()))
            }
            AtomicFact::NotEqualFact(_) => Ok(InferAtomicFactResult::NotEqualFact(Vec::new())),
            AtomicFact::NotLessFact(_) => Ok(InferAtomicFactResult::NotLessFact(Vec::new())),
            AtomicFact::NotGreaterFact(_) => Ok(InferAtomicFactResult::NotGreaterFact(Vec::new())),
            AtomicFact::NotLessEqualFact(_) => {
                Ok(InferAtomicFactResult::NotLessEqualFact(Vec::new()))
            }
            AtomicFact::NotGreaterEqualFact(_) => {
                Ok(InferAtomicFactResult::NotGreaterEqualFact(Vec::new()))
            }
            AtomicFact::NotIsSetFact(_) => Ok(InferAtomicFactResult::NotIsSetFact(Vec::new())),
            AtomicFact::NotIsNonemptySetFact(_) => {
                Ok(InferAtomicFactResult::NotIsNonemptySetFact(Vec::new()))
            }
            AtomicFact::NotIsFiniteSetFact(_) => {
                Ok(InferAtomicFactResult::NotIsFiniteSetFact(Vec::new()))
            }
            AtomicFact::NotInFact(_) => Ok(InferAtomicFactResult::NotInFact(Vec::new())),
            AtomicFact::NotSubsetFact(_) => Ok(InferAtomicFactResult::NotSubsetFact(Vec::new())),
            AtomicFact::NotSupersetFact(_) => {
                Ok(InferAtomicFactResult::NotSupersetFact(Vec::new()))
            }
            AtomicFact::NotProperSubsetFact(_) => {
                Ok(InferAtomicFactResult::NotProperSubsetFact(Vec::new()))
            }
            AtomicFact::NotProperSupersetFact(_) => {
                Ok(InferAtomicFactResult::NotProperSupersetFact(Vec::new()))
            }
            AtomicFact::NotPrimeFact(_) => Ok(InferAtomicFactResult::NotPrimeFact(Vec::new())),
            AtomicFact::NotCoprimeFact(_) => Ok(InferAtomicFactResult::NotCoprimeFact(Vec::new())),
            AtomicFact::NotDvdFact(_) => Ok(InferAtomicFactResult::NotDvdFact(Vec::new())),
            AtomicFact::NotInjectiveFact(_) => {
                Ok(InferAtomicFactResult::NotInjectiveFact(Vec::new()))
            }
            AtomicFact::NotSurjectiveFact(_) => {
                Ok(InferAtomicFactResult::NotSurjectiveFact(Vec::new()))
            }
            AtomicFact::NotBijectiveFact(_) => {
                Ok(InferAtomicFactResult::NotBijectiveFact(Vec::new()))
            }
            AtomicFact::NotIsChoiceFunctionForFact(_) => {
                Ok(InferAtomicFactResult::NotIsChoiceFunctionForFact(Vec::new()))
            }
        }
    }
}
