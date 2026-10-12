use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferEqualityResult, StoreInferredFactResult};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_equality_inference_rules(
        &self,
        rules: &[InferEqualityResult],
        source: &EqualFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        for (index, rule) in rules.iter().enumerate() {
            let group = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityInferences(rules),
                index,
            );
            let emitted = match rule {
                InferEqualityResult::AdditiveCancellation(rule) => {
                    self.compile_additive_inference(rule, source, compiled, &group)?
                }
                InferEqualityResult::NonzeroFactorCancellation(rule) => {
                    self.compile_nonzero_factor_inference(rule, source, compiled, &group)?
                }
                InferEqualityResult::SubtractiveCancellation(rule) => {
                    self.compile_subtractive_inference(rule, source, compiled, &group)?
                }
                InferEqualityResult::CommonDenominatorCancellation(rule) => {
                    self.compile_common_denominator_inference(rule, source, compiled, &group)?
                }
                InferEqualityResult::NonzeroNumeratorCancellation(rule) => {
                    self.compile_nonzero_numerator_inference(rule, source, compiled, &group)?
                }
                // Unsupported inference has no emitted producer and cannot be cited.
                InferEqualityResult::PositiveRealPower(_) => Vec::new(),
            };
            declarations.extend(emitted);
        }
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn cancellation_fact(
        &self,
        captured: &StoreInferredFactResult,
        position: &SourcePosition<'_>,
        route: &str,
    ) -> Result<Fact, LeanCompileError> {
        let derived = &captured.store;
        let fact = match derived {
            StoreFactResult::AtomicFact(stored) => match &stored.fact {
                AtomicFact::EqualFact(equal) => Fact::AtomicFact(equal.clone().into()),
                _ => return Err(LeanCompileError::unsupported(&format!("{route}Conclusion"))),
            },
            _ => return Err(LeanCompileError::unsupported(&format!("{route}Conclusion"))),
        };
        if self.resolve_fact(derived.primary_fact_id(), position)? != fact {
            return Err(LeanCompileError::new(
                &format!("{route}Identity"),
                "The captured cancellation store differs from its exact source fact ID.",
            ));
        }
        self.validate_store(derived, &fact)?;
        Ok(fact)
    }

    pub(in crate::compile_to_lean) fn compile_cancellation_members(
        &self,
        proofs: [&VerifyFactResult; 3],
        operands: [&Obj; 3],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut members = Vec::new();
        for (index, (proof, operand)) in proofs.into_iter().zip(operands).enumerate() {
            ensure_complex_member(&source_subject(proof)?, operand)?;
            let stage = SourcePosition {
                before: index,
                ..*position
            };
            members.push(self.compile_verify(proof, &stage)?.1);
        }
        Ok(members)
    }
}
