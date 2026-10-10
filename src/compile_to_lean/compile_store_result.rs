use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_parameter_store_capture(
        &self,
        result: &StoreHaveObjAndInferResult,
    ) -> Result<(), LeanCompileError> {
        let ids: Vec<_> = result
            .store_and_infer_results
            .iter()
            .flat_map(|store| store.stored_fact_ids())
            .collect();
        if ids != result.stored_fact_ids {
            return Err(LeanCompileError::new(
                "Parameters/StoreCapture",
                "The actual ordered store trees do not match their ID view.",
            ));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_parameter_inferences(
        &self,
        store: &StoreFactAndInferResult,
        member_fact: &Fact,
        member: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let rules = match &store.infer {
            InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) => rules,
            _ => return Ok(Vec::new()),
        };
        let mut declarations = Vec::new();
        for rule in rules {
            if let InferAtomicExceptEqualityResult::InFactSetBuilder(proof) = rule {
                declarations.extend(self.compile_set_builder_projections(
                    store,
                    proof,
                    member_fact,
                    member,
                    position,
                )?);
            }
            if let InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(sign) = rule {
                let source = match member_fact {
                    Fact::AtomicFact(AtomicFact::InFact(f))
                        if f.set == Obj::StandardSet(StandardSet::N) =>
                    {
                        f
                    }
                    _ => return Err(LeanCompileError::unsupported("Inference/SignedCarrier")),
                };
                if sign.derived.len() != 1 {
                    return Err(LeanCompileError::new(
                        "Inference/NaturalArity",
                        "Natural membership has exactly one nonnegative projection.",
                    ));
                }
                let derived = &sign.derived[0];
                let fact = self.resolve_fact(derived.primary_fact_id(), position)?;
                let bound = match &fact {
                    Fact::AtomicFact(AtomicFact::LessEqualFact(f))
                        if is_exact_zero(&f.left) && f.right.ir() == source.element.ir() =>
                    {
                        f
                    }
                    _ => {
                        return Err(LeanCompileError::new(
                            "Inference/NaturalSubject",
                            "The natural nonnegative projection has another endpoint.",
                        ))
                    }
                };
                self.validate_store(derived, &fact)?;
                let _ = bound;
                let compiled = (
                    self.fact_proposition(&fact, position)?,
                    format!(
                        "(Litex.naturalNonnegative {} {})",
                        self.compile_object_reference(&source.element, position)?,
                        member.1
                    ),
                );
                declarations.push(self.emit_internal_fact(&fact, &compiled, position));
            }
        }
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn validate_store(
        &self,
        store: &StoreFactAndInferResult,
        expected: &Fact,
    ) -> Result<(), LeanCompileError> {
        let actual = match &store.store {
            StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
            StoreFactResult::ForallFact(stored) => Fact::ForallFact(stored.fact.clone()),
            StoreFactResult::AndFact(_)
            | StoreFactResult::ChainFact(_)
            | StoreFactResult::OrFact(_)
            | StoreFactResult::ExistShapedFact(_)
            | StoreFactResult::NotForallFact(_)
            | StoreFactResult::ForallFactWithIff(_) => {
                return Err(LeanCompileError::unsupported("Store/Compound"))
            }
        };
        if &actual != expected || store.primary_fact_id() != expected.fact_id() {
            return Err(LeanCompileError::new(
                "Store/Subject",
                "The stored target differs from the replayed verification.",
            ));
        }
        // Additional inferred facts are not promoted to assumptions. A future
        // citation of an unsupported inference fails the original source-prefix lookup.
        Ok(())
    }
}
