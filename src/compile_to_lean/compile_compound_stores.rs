use crate::compile_to_lean::compile_compound_fact::chain_edge;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_compound_stores(
        &self,
        store: &StoreFactAndInferResult,
        source: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        self.validate_store(&store.store, source)?;
        let mut declarations = Vec::new();
        let components = match (&store.store, &store.infer, source) {
            (
                StoreFactResult::AndFact(stored),
                Some(InferResult::AndFact(inferred)),
                Fact::AndFact(source),
            ) => {
                if stored.components.len() != source.facts.len()
                    || inferred.components.len() != source.facts.len()
                    || source.facts.is_empty()
                {
                    return Err(LeanCompileError::unsupported("And/StoreArity"));
                }
                let mut components = Vec::new();
                for (index, component) in stored.components.iter().enumerate() {
                    if component.component_index != index
                        || component.fact_id != component.fact.fact_id()
                        || component.fact != source.facts[index]
                    {
                        return Err(LeanCompileError::new(
                            "And/StoreSubject",
                            "A stored component has another source index, subject or identity.",
                        ));
                    }
                    components.push((component.fact_id, component.fact.clone()));
                }
                components
            }
            (
                StoreFactResult::ChainFact(stored),
                Some(InferResult::ChainFact(inferred)),
                Fact::ChainFact(source),
            ) => {
                if stored.adjacent.len() != source.prop_names.len()
                    || inferred.adjacent_infers.len() != source.prop_names.len()
                    || source.prop_names.is_empty()
                {
                    return Err(LeanCompileError::unsupported("Chain/StoreArity"));
                }
                let mut components = Vec::new();
                for (index, component) in stored.adjacent.iter().enumerate() {
                    if component.edge_index != index
                        || component.fact_id != component.fact.fact_id()
                        || component.fact != chain_edge(source, index, component.fact_id)?
                    {
                        return Err(LeanCompileError::new("Chain/StoreSubject", "A stored edge has another source index, subject, orientation or identity."));
                    }
                    components.push((component.fact_id, component.fact.clone()));
                }
                components
            }
            _ => return Err(LeanCompileError::unsupported("Compound/StoreFamily")),
        };
        for (index, (id, atomic)) in components.iter().enumerate() {
            let fact = Fact::AtomicFact(atomic.clone());
            if self.resolve_fact(*id, position)? != fact {
                return Err(LeanCompileError::new(
                    "Compound/StoreIdentity",
                    "The stored projection differs from the exact registered source FactId.",
                ));
            }
            let projection = (
                self.fact_proposition(&fact, position)?,
                conjunction_projection(&compiled.1, index, components.len()),
            );
            declarations.push(self.emit_internal_fact_reference(&fact, &projection, position)?);
        }
        let group = SourcePosition::new(Some(position), SourceOwner::CompoundInference(store), 0);
        match &store.infer {
            Some(InferResult::AndFact(inferred)) => {
                for (index, infer) in inferred.components.iter().enumerate() {
                    let fact = Fact::AtomicFact(components[index].1.clone());
                    let prior = SourcePosition {
                        before: index,
                        ..group
                    };
                    let name = format!("h_{}", fact.fact_id().value());
                    let reference = if prior.is_local() {
                        name
                    } else {
                        self.context_application(&name, &prior)
                    };
                    let seed = (self.fact_proposition(&fact, &prior)?, reference);
                    let current = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::AtomicInference(&fact, infer),
                        0,
                    );
                    declarations
                        .extend(self.compile_atomic_inferences(infer, &fact, &seed, &current)?);
                }
            }
            Some(InferResult::ChainFact(inferred)) => {
                for (index, captured) in inferred.adjacent_infers.iter().enumerate() {
                    let Fact::AtomicFact(atomic) = &captured.fact else {
                        return Err(LeanCompileError::unsupported("Chain/InferenceSeedFamily"));
                    };
                    if captured.edge_index != index
                        || *atomic != chain_edge(&inferred_chain(store)?, index, atomic.fact_id())?
                    {
                        return Err(LeanCompileError::new(
                            "Chain/InferenceSeed",
                            "An inference seed differs from its captured original adjacent edge.",
                        ));
                    }
                    let prior = SourcePosition {
                        before: index,
                        ..group
                    };
                    let name = format!("h_{}", components[index].0.value());
                    let reference = if prior.is_local() {
                        name
                    } else {
                        self.context_application(&name, &prior)
                    };
                    let seed = (self.fact_proposition(&captured.fact, &prior)?, reference);
                    declarations.push(self.emit_internal_fact_reference(
                        &captured.fact,
                        &seed,
                        &prior,
                    )?);
                    let name = format!("h_{}", captured.fact.fact_id().value());
                    let reference = if prior.is_local() {
                        name
                    } else {
                        self.context_application(&name, &prior)
                    };
                    let seed = (seed.0, reference);
                    let current = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::AtomicInference(&captured.fact, &captured.infer),
                        0,
                    );
                    declarations.extend(self.compile_atomic_inferences(
                        &captured.infer,
                        &captured.fact,
                        &seed,
                        &current,
                    )?);
                }
                declarations.extend(self.compile_chain_closures(store, &group)?);
            }
            _ => unreachable!("the original compound family was checked"),
        }
        Ok(declarations)
    }

    // Index projections are part of storage, including for a derived And/Chain.
    pub(in crate::compile_to_lean) fn compile_stored_projections(
        &self,
        store: &StoreFactResult,
        source: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if !matches!(source, Fact::AndFact(_) | Fact::ChainFact(_)) {
            return Ok(Vec::new());
        }
        self.validate_store(store, source)?;
        let components = store.atomic_components();
        let expected = match source {
            Fact::AndFact(fact) => fact.facts.len(),
            Fact::ChainFact(fact) => fact.prop_names.len(),
            _ => unreachable!(),
        };
        if components.len() != expected || expected == 0 {
            return Err(LeanCompileError::unsupported("Compound/StoreArity"));
        }
        let mut declarations = Vec::new();
        for (index, (id, atomic)) in components.iter().enumerate() {
            let expected_atomic = match source {
                Fact::AndFact(fact) => fact.facts[index].clone(),
                Fact::ChainFact(fact) => chain_edge(fact, index, *id)?,
                _ => unreachable!(),
            };
            if *atomic != expected_atomic || *id != atomic.fact_id() {
                return Err(LeanCompileError::unsupported("Compound/StoreSubject"));
            }
            let fact = Fact::AtomicFact(atomic.clone());
            if self.resolve_fact(*id, position)? != fact {
                return Err(LeanCompileError::unsupported("Compound/StoreIdentity"));
            }
            let projection = (
                self.fact_proposition(&fact, position)?,
                conjunction_projection(&compiled.1, index, components.len()),
            );
            declarations.push(self.emit_internal_fact(&fact, &projection, position)?);
        }
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn compile_atomic_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(atomic) = seed else {
            return Err(LeanCompileError::unsupported(
                "Compound/AtomicInferenceFamily",
            ));
        };
        let family_matches = match infer {
            InferAtomicFactResult::IsMatrixInvFact(_) => {
                matches!(atomic, AtomicFact::IsMatrixInvFact(_))
            }
            InferAtomicFactResult::NotIsMatrixInvFact(_) => {
                matches!(atomic, AtomicFact::NotIsMatrixInvFact(_))
            }
            InferAtomicFactResult::MatrixInversibleFact(_) => {
                matches!(atomic, AtomicFact::MatrixInversibleFact(_))
            }
            InferAtomicFactResult::NotMatrixInversibleFact(_) => {
                matches!(atomic, AtomicFact::NotMatrixInversibleFact(_))
            }
            InferAtomicFactResult::CommRingFact(_) => matches!(atomic, AtomicFact::CommRingFact(_)),
            InferAtomicFactResult::NotCommRingFact(_) => {
                matches!(atomic, AtomicFact::NotCommRingFact(_))
            }
            InferAtomicFactResult::MultivariableAnalysisFact(_) => {
                matches!(atomic, AtomicFact::MultivariableAnalysisFact(_))
            }
            InferAtomicFactResult::NotMultivariableAnalysisFact(_) => {
                matches!(atomic, AtomicFact::NotMultivariableAnalysisFact(_))
            }
            InferAtomicFactResult::RealSetBoundFact(_) => {
                matches!(atomic, AtomicFact::RealSetBoundFact(_))
            }
            InferAtomicFactResult::NotRealSetBoundFact(_) => {
                matches!(atomic, AtomicFact::NotRealSetBoundFact(_))
            }
            InferAtomicFactResult::RealSetBoundedFact(_) => {
                matches!(atomic, AtomicFact::RealSetBoundedFact(_))
            }
            InferAtomicFactResult::NotRealSetBoundedFact(_) => {
                matches!(atomic, AtomicFact::NotRealSetBoundedFact(_))
            }
            InferAtomicFactResult::SequenceAnalysisFact(_) => {
                matches!(atomic, AtomicFact::SequenceAnalysisFact(_))
            }
            InferAtomicFactResult::NotSequenceAnalysisFact(_) => {
                matches!(atomic, AtomicFact::NotSequenceAnalysisFact(_))
            }
            InferAtomicFactResult::RealAccumulationFact(_) => {
                matches!(atomic, AtomicFact::RealAccumulationFact(_))
            }
            InferAtomicFactResult::NotRealAccumulationFact(_) => {
                matches!(atomic, AtomicFact::NotRealAccumulationFact(_))
            }
            InferAtomicFactResult::HasRiemannIntegralFact(_) => {
                matches!(atomic, AtomicFact::HasRiemannIntegralFact(_))
            }
            InferAtomicFactResult::NotHasRiemannIntegralFact(_) => {
                matches!(atomic, AtomicFact::NotHasRiemannIntegralFact(_))
            }
            InferAtomicFactResult::FunctionRiemannIntegrableFact(_) => {
                matches!(atomic, AtomicFact::FunctionRiemannIntegrableFact(_))
            }
            InferAtomicFactResult::NotFunctionRiemannIntegrableFact(_) => {
                matches!(atomic, AtomicFact::NotFunctionRiemannIntegrableFact(_))
            }
            InferAtomicFactResult::HasDerivativeAtFact(_) => {
                matches!(atomic, AtomicFact::HasDerivativeAtFact(_))
            }
            InferAtomicFactResult::NotHasDerivativeAtFact(_) => {
                matches!(atomic, AtomicFact::NotHasDerivativeAtFact(_))
            }
            InferAtomicFactResult::FunctionDifferentiableAtFact(_) => {
                matches!(atomic, AtomicFact::FunctionDifferentiableAtFact(_))
            }
            InferAtomicFactResult::NotFunctionDifferentiableAtFact(_) => {
                matches!(atomic, AtomicFact::NotFunctionDifferentiableAtFact(_))
            }
            InferAtomicFactResult::FunctionContinuousAtFact(_) => {
                matches!(atomic, AtomicFact::FunctionContinuousAtFact(_))
            }
            InferAtomicFactResult::NotFunctionContinuousAtFact(_) => {
                matches!(atomic, AtomicFact::NotFunctionContinuousAtFact(_))
            }
            InferAtomicFactResult::FunctionContinuousFact(_) => {
                matches!(atomic, AtomicFact::FunctionContinuousFact(_))
            }
            InferAtomicFactResult::NotFunctionContinuousFact(_) => {
                matches!(atomic, AtomicFact::NotFunctionContinuousFact(_))
            }
            InferAtomicFactResult::FunctionLipschitzFact(_) => {
                matches!(atomic, AtomicFact::FunctionLipschitzFact(_))
            }
            InferAtomicFactResult::NotFunctionLipschitzFact(_) => {
                matches!(atomic, AtomicFact::NotFunctionLipschitzFact(_))
            }
            InferAtomicFactResult::HasFunctionLimitFact(_) => {
                matches!(atomic, AtomicFact::HasFunctionLimitFact(_))
            }
            InferAtomicFactResult::NotHasFunctionLimitFact(_) => {
                matches!(atomic, AtomicFact::NotHasFunctionLimitFact(_))
            }
            InferAtomicFactResult::HasSequenceLimitFact(_) => {
                matches!(atomic, AtomicFact::HasSequenceLimitFact(_))
            }
            InferAtomicFactResult::HasSequenceLimsupFact(_) => {
                matches!(atomic, AtomicFact::HasSequenceLimsupFact(_))
            }
            InferAtomicFactResult::HasSequenceLiminfFact(_) => {
                matches!(atomic, AtomicFact::HasSequenceLiminfFact(_))
            }
            InferAtomicFactResult::NotHasSequenceLimitFact(_) => {
                matches!(atomic, AtomicFact::NotHasSequenceLimitFact(_))
            }
            InferAtomicFactResult::NotHasSequenceLimsupFact(_) => {
                matches!(atomic, AtomicFact::NotHasSequenceLimsupFact(_))
            }
            InferAtomicFactResult::NotHasSequenceLiminfFact(_) => {
                matches!(atomic, AtomicFact::NotHasSequenceLiminfFact(_))
            }
            InferAtomicFactResult::NormalAtomicFact(_) => {
                matches!(atomic, AtomicFact::NormalAtomicFact(_))
            }
            InferAtomicFactResult::EqualFact(_) => matches!(atomic, AtomicFact::EqualFact(_)),
            InferAtomicFactResult::LessFact(_) => matches!(atomic, AtomicFact::LessFact(_)),
            InferAtomicFactResult::GreaterFact(_) => matches!(atomic, AtomicFact::GreaterFact(_)),
            InferAtomicFactResult::LessEqualFact(_) => {
                matches!(atomic, AtomicFact::LessEqualFact(_))
            }
            InferAtomicFactResult::GreaterEqualFact(_) => {
                matches!(atomic, AtomicFact::GreaterEqualFact(_))
            }
            InferAtomicFactResult::IsSetFact(_) => matches!(atomic, AtomicFact::IsSetFact(_)),
            InferAtomicFactResult::IsNonemptySetFact(_) => {
                matches!(atomic, AtomicFact::IsNonemptySetFact(_))
            }
            InferAtomicFactResult::IsFiniteSetFact(_) => {
                matches!(atomic, AtomicFact::IsFiniteSetFact(_))
            }
            InferAtomicFactResult::InFact(_) => matches!(atomic, AtomicFact::InFact(_)),
            InferAtomicFactResult::SubsetFact(_) => matches!(atomic, AtomicFact::SubsetFact(_)),
            InferAtomicFactResult::SupersetFact(_) => matches!(atomic, AtomicFact::SupersetFact(_)),
            InferAtomicFactResult::ProperSubsetFact(_) => {
                matches!(atomic, AtomicFact::ProperSubsetFact(_))
            }
            InferAtomicFactResult::ProperSupersetFact(_) => {
                matches!(atomic, AtomicFact::ProperSupersetFact(_))
            }
            InferAtomicFactResult::PrimeFact(_) => matches!(atomic, AtomicFact::PrimeFact(_)),
            InferAtomicFactResult::CoprimeFact(_) => matches!(atomic, AtomicFact::CoprimeFact(_)),
            InferAtomicFactResult::DvdFact(_) => matches!(atomic, AtomicFact::DvdFact(_)),
            InferAtomicFactResult::InjectiveFact(_) => {
                matches!(atomic, AtomicFact::InjectiveFact(_))
            }
            InferAtomicFactResult::SurjectiveFact(_) => {
                matches!(atomic, AtomicFact::SurjectiveFact(_))
            }
            InferAtomicFactResult::BijectiveFact(_) => {
                matches!(atomic, AtomicFact::BijectiveFact(_))
            }
            InferAtomicFactResult::IsChoiceFunctionForFact(_) => {
                matches!(atomic, AtomicFact::IsChoiceFunctionForFact(_))
            }
            InferAtomicFactResult::NotNormalAtomicFact(_) => {
                matches!(atomic, AtomicFact::NotNormalAtomicFact(_))
            }
            InferAtomicFactResult::NotEqualFact(_) => matches!(atomic, AtomicFact::NotEqualFact(_)),
            InferAtomicFactResult::NotLessFact(_) => matches!(atomic, AtomicFact::NotLessFact(_)),
            InferAtomicFactResult::NotGreaterFact(_) => {
                matches!(atomic, AtomicFact::NotGreaterFact(_))
            }
            InferAtomicFactResult::NotLessEqualFact(_) => {
                matches!(atomic, AtomicFact::NotLessEqualFact(_))
            }
            InferAtomicFactResult::NotGreaterEqualFact(_) => {
                matches!(atomic, AtomicFact::NotGreaterEqualFact(_))
            }
            InferAtomicFactResult::NotIsSetFact(_) => matches!(atomic, AtomicFact::NotIsSetFact(_)),
            InferAtomicFactResult::NotIsNonemptySetFact(_) => {
                matches!(atomic, AtomicFact::NotIsNonemptySetFact(_))
            }
            InferAtomicFactResult::NotIsFiniteSetFact(_) => {
                matches!(atomic, AtomicFact::NotIsFiniteSetFact(_))
            }
            InferAtomicFactResult::NotInFact(_) => matches!(atomic, AtomicFact::NotInFact(_)),
            InferAtomicFactResult::NotSubsetFact(_) => {
                matches!(atomic, AtomicFact::NotSubsetFact(_))
            }
            InferAtomicFactResult::NotSupersetFact(_) => {
                matches!(atomic, AtomicFact::NotSupersetFact(_))
            }
            InferAtomicFactResult::NotProperSubsetFact(_) => {
                matches!(atomic, AtomicFact::NotProperSubsetFact(_))
            }
            InferAtomicFactResult::NotProperSupersetFact(_) => {
                matches!(atomic, AtomicFact::NotProperSupersetFact(_))
            }
            InferAtomicFactResult::NotPrimeFact(_) => matches!(atomic, AtomicFact::NotPrimeFact(_)),
            InferAtomicFactResult::NotCoprimeFact(_) => {
                matches!(atomic, AtomicFact::NotCoprimeFact(_))
            }
            InferAtomicFactResult::NotDvdFact(_) => matches!(atomic, AtomicFact::NotDvdFact(_)),
            InferAtomicFactResult::NotInjectiveFact(_) => {
                matches!(atomic, AtomicFact::NotInjectiveFact(_))
            }
            InferAtomicFactResult::NotSurjectiveFact(_) => {
                matches!(atomic, AtomicFact::NotSurjectiveFact(_))
            }
            InferAtomicFactResult::NotBijectiveFact(_) => {
                matches!(atomic, AtomicFact::NotBijectiveFact(_))
            }
            InferAtomicFactResult::NotIsChoiceFunctionForFact(_) => {
                matches!(atomic, AtomicFact::NotIsChoiceFunctionForFact(_))
            }
        };
        if !family_matches {
            return Err(LeanCompileError::unsupported(
                "Compound/AtomicInferenceFamily",
            ));
        }
        match infer {
            InferAtomicFactResult::IsMatrixInvFact(_)
            | InferAtomicFactResult::MatrixInversibleFact(_) => {
                self.compile_matrix_inverse_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::NotIsMatrixInvFact(_)
            | InferAtomicFactResult::NotMatrixInversibleFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::CommRingFact(_) | InferAtomicFactResult::NotCommRingFact(_) => {
                Err(LeanCompileError::unsupported("Infer/CommRing"))
            }
            InferAtomicFactResult::MultivariableAnalysisFact(_) => {
                if matches!(seed,Fact::AtomicFact(a) if super::compile_multivariable_continuity::parts(a).is_some())
                {
                    self.compile_multivariable_continuity_inferences(
                        infer, seed, compiled, position,
                    )
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_multivariable_differentiability::parts(a).is_some())
                {
                    self.compile_multivariable_differentiability_inferences(
                        infer, seed, compiled, position,
                    )
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_total_differential::parts(a).is_some())
                {
                    self.compile_total_differential_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_scalar_differential::parts(a).is_some())
                {
                    self.compile_scalar_differential_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_laplacian::parts(a).is_some())
                {
                    self.compile_laplacian_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_hessian::parts(a).is_some())
                {
                    self.compile_hessian_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_second_partial::parts(a).is_some())
                {
                    self.compile_second_partial_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_curl::parts(a).is_some())
                {
                    self.compile_curl_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_divergence::parts(a).is_some())
                {
                    self.compile_divergence_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_jacobian::parts(a).is_some())
                {
                    self.compile_jacobian_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_gradient::parts(a).is_some())
                {
                    self.compile_gradient_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_partial_derivative::parts(a).is_some())
                {
                    self.compile_partial_derivative_inferences(infer, seed, compiled, position)
                } else if matches!(seed,Fact::AtomicFact(a) if super::compile_multivariable_vector_limit::parts(a).is_some())
                {
                    self.compile_multivariable_vector_inferences(infer, seed, compiled, position)
                } else {
                    self.compile_multivariable_scalar_inferences(infer, seed, compiled, position)
                }
            }
            InferAtomicFactResult::NotMultivariableAnalysisFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::RealSetBoundFact(_)
            | InferAtomicFactResult::RealSetBoundedFact(_) => {
                self.compile_real_bound_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::NotRealSetBoundFact(_)
            | InferAtomicFactResult::NotRealSetBoundedFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::SequenceAnalysisFact(_) => {
                self.compile_sequence_analysis_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::NotSequenceAnalysisFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::RealAccumulationFact(_) => {
                self.compile_real_accumulation_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::NotRealAccumulationFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::HasRiemannIntegralFact(_) => {
                self.compile_riemann_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::FunctionRiemannIntegrableFact(_) => {
                self.compile_riemann_integrability_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::NotHasRiemannIntegralFact(_)
            | InferAtomicFactResult::NotFunctionRiemannIntegrableFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::NotHasDerivativeAtFact(_)
            | InferAtomicFactResult::NotFunctionDifferentiableAtFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::HasDerivativeAtFact(_) => {
                self.compile_derivative_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::FunctionDifferentiableAtFact(_) => {
                self.compile_differentiability_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::FunctionContinuousAtFact(_) => {
                self.compile_function_continuity_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::NotFunctionContinuousAtFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::FunctionContinuousFact(_) => {
                if matches!(seed, Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) if f.property == FunctionContinuityProperty::UniformContinuous)
                {
                    self.compile_uniform_continuity_inferences(infer, seed, compiled, position)
                } else {
                    self.compile_global_continuity_inferences(infer, seed, compiled, position)
                }
            }
            InferAtomicFactResult::NotFunctionContinuousFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::FunctionLipschitzFact(_) => {
                self.compile_lipschitz_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::NotFunctionLipschitzFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::HasFunctionLimitFact(_)
            | InferAtomicFactResult::NotHasFunctionLimitFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::HasSequenceLimitFact(_)
            | InferAtomicFactResult::NotHasSequenceLimitFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::HasSequenceLimsupFact(_)
            | InferAtomicFactResult::NotHasSequenceLimsupFact(_)
            | InferAtomicFactResult::HasSequenceLiminfFact(_)
            | InferAtomicFactResult::NotHasSequenceLiminfFact(_) => Ok(Vec::new()),
            InferAtomicFactResult::EqualFact(rules) => {
                let AtomicFact::EqualFact(source) = atomic else {
                    unreachable!()
                };
                self.compile_equality_inference_rules(rules, source, compiled, position)
            }
            InferAtomicFactResult::NormalAtomicFact(rules) => {
                self.compile_prop_inference_rules(rules, seed, compiled, position)
            }
            InferAtomicFactResult::InFact(rules) => {
                self.compile_membership_inference_rules(rules, seed, compiled, position)
            }
            InferAtomicFactResult::LessFact(_)
            | InferAtomicFactResult::GreaterFact(_)
            | InferAtomicFactResult::LessEqualFact(_)
            | InferAtomicFactResult::GreaterEqualFact(_) => {
                self.compile_order_bound_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::InjectiveFact(_)
            | InferAtomicFactResult::SurjectiveFact(_)
            | InferAtomicFactResult::BijectiveFact(_) => {
                self.compile_mapping_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::ProperSubsetFact(_)
            | InferAtomicFactResult::ProperSupersetFact(_) => {
                self.compile_proper_inclusion_inferences(infer, seed, compiled, position)
            }
            InferAtomicFactResult::SubsetFact(rules) => {
                self.compile_subset_inferences(rules, seed, compiled, position)
            }
            InferAtomicFactResult::PrimeFact(rules) => {
                self.compile_prime_inferences(rules, seed, compiled, position)
            }
            InferAtomicFactResult::DvdFact(rules) => {
                self.compile_dvd_inferences(rules, seed, compiled, position)
            }
            InferAtomicFactResult::IsSetFact(_)
            | InferAtomicFactResult::IsNonemptySetFact(_)
            | InferAtomicFactResult::IsFiniteSetFact(_)
            | InferAtomicFactResult::SupersetFact(_)
            | InferAtomicFactResult::CoprimeFact(_)
            | InferAtomicFactResult::IsChoiceFunctionForFact(_)
            | InferAtomicFactResult::NotNormalAtomicFact(_)
            | InferAtomicFactResult::NotEqualFact(_)
            | InferAtomicFactResult::NotLessFact(_)
            | InferAtomicFactResult::NotGreaterFact(_)
            | InferAtomicFactResult::NotLessEqualFact(_)
            | InferAtomicFactResult::NotGreaterEqualFact(_)
            | InferAtomicFactResult::NotIsSetFact(_)
            | InferAtomicFactResult::NotIsNonemptySetFact(_)
            | InferAtomicFactResult::NotIsFiniteSetFact(_)
            | InferAtomicFactResult::NotInFact(_)
            | InferAtomicFactResult::NotSubsetFact(_)
            | InferAtomicFactResult::NotSupersetFact(_)
            | InferAtomicFactResult::NotProperSubsetFact(_)
            | InferAtomicFactResult::NotProperSupersetFact(_)
            | InferAtomicFactResult::NotPrimeFact(_)
            | InferAtomicFactResult::NotCoprimeFact(_)
            | InferAtomicFactResult::NotDvdFact(_)
            | InferAtomicFactResult::NotInjectiveFact(_)
            | InferAtomicFactResult::NotSurjectiveFact(_)
            | InferAtomicFactResult::NotBijectiveFact(_)
            | InferAtomicFactResult::NotIsChoiceFunctionForFact(_) => Ok(Vec::new()),
        }
    }
}

fn inferred_chain(store: &StoreFactAndInferResult) -> Result<ChainFact, LeanCompileError> {
    match &store.store {
        StoreFactResult::ChainFact(stored) => Ok(stored.fact.clone()),
        _ => Err(LeanCompileError::unsupported("Chain/StoreFamily")),
    }
}

impl LitexToLeanCompiler {
    fn compile_singleton_member_inference(
        &self,
        source: &Fact,
        compiled: &(String, String),
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(member)) = source else {
            return Err(LeanCompileError::unsupported("Singleton/InferenceSource"));
        };
        let Obj::SetFormer(SetFormer::ListSet(set)) = &member.set else {
            return Err(LeanCompileError::unsupported("Singleton/InferenceCarrier"));
        };
        let [element] = set.list.as_slice() else {
            return Err(LeanCompileError::unsupported("Singleton/InferenceArity"));
        };
        let StoreFactResult::AtomicFact(stored) = store else {
            return Err(LeanCompileError::unsupported("Singleton/InferenceStore"));
        };
        let AtomicFact::EqualFact(equal) = &stored.fact else {
            return Err(LeanCompileError::unsupported(
                "Singleton/InferenceConclusion",
            ));
        };
        if equal.left.ir() != member.element.ir()
            || equal.right.ir() != element.ir()
            || equal.fact_id == member.fact_id
        {
            return Err(LeanCompileError::unsupported("Singleton/InferenceSubject"));
        }
        let fact = Fact::AtomicFact(stored.fact.clone());
        self.validate_store(store, &fact)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::InferredStore(store),
            usize::MAX,
        );
        let receiver = self.compile_object_reference(&member.element, &formed)?;
        let element = self.compile_object_reference(element, &formed)?;
        let term = format!("(by\n  have _member : M.mem (Litex.denote {receiver}) (Litex.SetSemantics.insertValue (Litex.denote {element}) (Litex.SetSemantics.emptyValue (M := M))) := {}\n  exact ((Litex.SetSemantics.insert_members _ _ _).mp _member).elim (fun h => h) (fun h => False.elim (Litex.SetSemantics.empty_members _ h)))",compiled.1);
        Ok(vec![self.emit_internal_fact(
            &fact,
            &(format!("Litex.Same {receiver} {element}"), term),
            &formed,
        )?])
    }

    pub(in crate::compile_to_lean) fn compile_membership_inference_rules(
        &self,
        rules: &[InferInFactResult],
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(atomic @ AtomicFact::InFact(_)) = seed else {
            return Err(LeanCompileError::unsupported("Inference/MembershipSeed"));
        };
        let mut declarations = Vec::new();
        let mut completed = position.before;
        if rules
            .iter()
            .any(|rule| !rule.projected_membership_consequences().is_empty())
        {
            return Err(LeanCompileError::unsupported(
                "Inference/ProjectedMembershipConsequences",
            ));
        }
        for rule in rules {
            let prior = SourcePosition {
                before: completed,
                ..*position
            };
            match rule {
                InferInFactResult::EqualFnSetExpand(proof) => {
                    let AtomicFact::InFact(source) = atomic else {
                        unreachable!()
                    };
                    let mut transport_before = prior.before;
                    for transport in &proof.transports {
                        let at = SourcePosition {
                            before: transport_before,
                            ..prior
                        };
                        if transport.membership_fact_id != source.fact_id {
                            return Err(LeanCompileError::unsupported("EqualFnSetExpand/Source"));
                        }
                        let store = &transport.derived.store;
                        let target = self.resolve_fact(store.primary_fact_id(), &at)?;
                        let Fact::AtomicFact(AtomicFact::InFact(member)) = &target else {
                            return Err(LeanCompileError::unsupported("EqualFnSetExpand/Target"));
                        };
                        if member.element != source.element || member.fact_id == source.fact_id {
                            return Err(LeanCompileError::unsupported("EqualFnSetExpand/Subject"));
                        }
                        self.validate_store(store, &target)?;
                        let equality = self.compile_equality_path(
                            &source.set,
                            &member.set,
                            &transport.carrier_equal,
                            &at,
                        )?;
                        let receiver = self.compile_object_reference(&source.element, &at)?;
                        let target_compiled = (
                            self.fact_proposition(&target, &at)?,
                            format!("(Eq.mp (congrArg (fun _set => M.mem (Litex.denote {receiver}) _set) {equality}) {})", compiled.1),
                        );
                        declarations.push(self.emit_internal_fact(
                            &target,
                            &target_compiled,
                            &at,
                        )?);
                        transport_before += 1;
                        let after = SourcePosition {
                            before: transport_before,
                            ..prior
                        };
                        declarations.extend(self.compile_membership_inference_rules(
                            &transport.expansions,
                            &target,
                            &target_compiled,
                            &after,
                        )?);
                        transport_before += transport
                            .expansions
                            .iter()
                            .map(|r| r.stored_conclusions().len())
                            .sum::<usize>();
                    }
                }
                InferInFactResult::PowerSet(p) => {
                    declarations
                        .extend(self.compile_power_set_inference(p, seed, compiled, &prior)?);
                }
                InferInFactResult::Preimage(p) => {
                    declarations.extend(self.compile_preimage_inference(
                        false,
                        p.source_fact_id,
                        &p.source_equal,
                        &p.construction,
                        &p.derived,
                        seed,
                        compiled,
                        &prior,
                    )?)
                }
                InferInFactResult::PreimageSet(p) => {
                    declarations.extend(self.compile_preimage_inference(
                        true,
                        p.source_fact_id,
                        &p.source_equal,
                        &p.construction,
                        &p.derived,
                        seed,
                        compiled,
                        &prior,
                    )?)
                }
                InferInFactResult::Template(proof) => {
                    declarations.extend(
                        self.compile_template_membership_inference(proof, seed, compiled, &prior)?,
                    );
                }
                InferInFactResult::SignedStandardSetSign(sign) => {
                    declarations
                        .extend(self.compile_natural_sign_inference(sign, seed, compiled, &prior)?);
                }
                InferInFactResult::SetBuilder(proof) => {
                    declarations.extend(
                        self.compile_set_builder_projections(proof, seed, compiled, &prior)?,
                    );
                }
                InferInFactResult::CartCoordinates(proof) => {
                    declarations.extend(
                        self.compile_cart_coordinate_inferences(proof, seed, compiled, &prior)?,
                    );
                }
                InferInFactResult::FnRange(proof) => {
                    declarations
                        .extend(self.compile_range_inference(proof, seed, compiled, &prior)?);
                }
                InferInFactResult::SeqExpand(_)
                | InferInFactResult::FiniteSeqExpand(_)
                | InferInFactResult::MatrixExpand(_) => {
                    declarations
                        .extend(self.compile_sequence_inference(rule, seed, compiled, &prior)?);
                }
                InferInFactResult::RealInterval(p) => {
                    declarations.extend(self.compile_real_interval_inference(
                        &[&p.real_membership, &p.lower_bound, &p.upper_bound],
                        seed,
                        compiled,
                        &prior,
                    )?);
                }
                InferInFactResult::OneSideRealInterval(p) => {
                    declarations.extend(self.compile_real_interval_inference(
                        &[&p.real_membership, &p.bound],
                        seed,
                        compiled,
                        &prior,
                    )?);
                }
                InferInFactResult::Range(proof) => {
                    declarations.extend(self.compile_integer_interval_inference(
                        &proof.bounds,
                        false,
                        seed,
                        compiled,
                        &prior,
                    )?);
                }
                InferInFactResult::ClosedRange(proof) => {
                    declarations.extend(self.compile_integer_interval_inference(
                        &proof.bounds,
                        true,
                        seed,
                        compiled,
                        &prior,
                    )?);
                }
                InferInFactResult::ListSetSingletonEqual(proof) => {
                    declarations.extend(self.compile_singleton_member_inference(
                        seed,
                        compiled,
                        &proof.derived.store,
                        &prior,
                    )?);
                }
                InferInFactResult::SetMinusSplit(proof) => {
                    declarations
                        .extend(self.compile_set_minus_inference(proof, seed, compiled, &prior)?);
                }
                InferInFactResult::IntersectBoth(proof) => {
                    declarations.extend(
                        self.compile_intersection_inference(proof, seed, compiled, &prior)?,
                    );
                }
                InferInFactResult::UnionOr(proof) => {
                    let AtomicFact::InFact(member) = atomic else {
                        unreachable!()
                    };
                    let Obj::SetOperator(SetOperator::Union(union)) = &member.set else {
                        return Err(LeanCompileError::unsupported("Inference/UnionSource"));
                    };
                    let fact = self.resolve_fact(proof.derived.primary_fact_id(), &prior)?;
                    let Fact::OrFact(or) = &fact else {
                        return Err(LeanCompileError::unsupported("Inference/UnionConclusion"));
                    };
                    if or.facts.len() != 2 || or.facts.iter().zip([&union.left, &union.right]).any(|(branch, set)| {
                                !matches!(branch, AndChainAtomicFact::AtomicFact(AtomicFact::InFact(f))
                                    if f.element.ir() == member.element.ir() && f.set.ir() == set.ir())
                            }) {
                                return Err(LeanCompileError::new("Inference/UnionConclusion", "The original union projection has different ordered membership branches."));
                            }
                    self.validate_store(&proof.derived.store, &fact)?;
                    let term = format!(
                        "((Litex.inUnion_iff {} {} {}).mp {})",
                        self.compile_object_reference(&member.element, &prior)?,
                        self.compile_object_reference(&union.left, &prior)?,
                        self.compile_object_reference(&union.right, &prior)?,
                        compiled.1
                    );
                    let formed = SourcePosition::new(
                        Some(&prior),
                        SourceOwner::InferredStore(&proof.derived.store),
                        usize::MAX,
                    );
                    declarations.push(self.emit_internal_fact(
                        &fact,
                        &(self.fact_proposition(&fact, &formed)?, term),
                        &formed,
                    )?);
                }
                _ => {}
            }
            if matches!(
                rule,
                InferInFactResult::Template(_)
                    | InferInFactResult::EqualFnSetExpand(_)
                    | InferInFactResult::SetBuilder(_)
                    | InferInFactResult::PowerSet(_)
                    | InferInFactResult::Preimage(_)
                    | InferInFactResult::PreimageSet(_)
                    | InferInFactResult::SignedStandardSetSign(_)
                    | InferInFactResult::CartCoordinates(_)
                    | InferInFactResult::FnRange(_)
                    | InferInFactResult::RealInterval(_)
                    | InferInFactResult::OneSideRealInterval(_)
                    | InferInFactResult::SeqExpand(_)
                    | InferInFactResult::FiniteSeqExpand(_)
                    | InferInFactResult::MatrixExpand(_)
                    | InferInFactResult::Range(_)
                    | InferInFactResult::ClosedRange(_)
                    | InferInFactResult::UnionOr(_)
                    | InferInFactResult::IntersectBoth(_)
                    | InferInFactResult::SetMinusSplit(_)
                    | InferInFactResult::ListSetSingletonEqual(_)
            ) {
                completed += rule.stored_conclusions().len();
            }
        }
        Ok(declarations)
    }
}
