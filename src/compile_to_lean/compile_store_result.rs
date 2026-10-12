use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferAtomicFactResult, InferFactResult,
};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_stored_inferences(
        &self,
        store: &StoreFactAndInferResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        match &store.infer {
            None => self.compile_stored_projections(&store.store, seed, compiled, position),
            Some(InferFactResult::AtomicFact(infer)) => {
                self.validate_store(&store.store, seed)?;
                let current = SourcePosition::new(
                    Some(position),
                    SourceOwner::AtomicInference(seed, infer),
                    0,
                );
                self.compile_atomic_inferences(infer, seed, compiled, &current)
            }
            Some(InferFactResult::AndFact(_)) | Some(InferFactResult::ChainFact(_)) => {
                self.compile_compound_stores(store, seed, compiled, position)
            }
            _ => self.compile_prop_inferences(store, seed, compiled, position),
        }
    }

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
        let mut declarations =
            self.compile_set_builder_parameter_inferences(store, member_fact, member, position)?;
        let (infer, rules) = match &store.infer {
            Some(InferFactResult::AtomicFact(
                infer @ InferAtomicFactResult::ExceptEquality(rules),
            )) => (infer, rules),
            _ => return Ok(declarations),
        };
        for (index, rule) in rules.iter().enumerate() {
            if let InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(sign) = rule {
                // Builder projections precede the sign rule in this original
                // membership dispatcher. Keep the sign's own WD/store pending.
                let completed = rules[..index]
                    .iter()
                    .filter_map(|rule| match rule {
                        InferAtomicExceptEqualityResult::InFactSetBuilder(proof) => Some(proof),
                        _ => None,
                    })
                    .flat_map(|proof| &proof.steps)
                    .map(|step| step.derived.len())
                    .sum();
                let pending = SourcePosition::new(
                    Some(position),
                    SourceOwner::AtomicInference(member_fact, infer),
                    completed,
                );
                declarations.extend(self.compile_natural_sign_inference(
                    sign,
                    member_fact,
                    member,
                    &pending,
                )?);
            }
        }
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn compile_set_builder_parameter_inferences(
        &self,
        store: &StoreFactAndInferResult,
        member_fact: &Fact,
        member: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let rules = match &store.infer {
            Some(InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules))) => {
                rules
            }
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
        }
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn compile_natural_sign_inference(
        &self,
        sign: &crate::store_fact_and_infer::InferInFactSignedStandardSetSignResult,
        member_fact: &Fact,
        member: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
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
        let captured = &sign.derived[0];
        let derived = &captured.store;
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
        self.compile_fact_wd(&captured.well_defined, &fact, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::FactWD(&captured.well_defined),
            usize::MAX,
        );
        let _ = bound;
        let compiled = (
            self.fact_proposition(&fact, &formed)?,
            format!(
                "(Litex.naturalNonnegative {} {})",
                self.compile_object_reference(&source.element, &formed)?,
                member.1
            ),
        );
        declarations.push(self.emit_internal_fact(&fact, &compiled, &formed));
        Ok(declarations)
    }

    pub(in crate::compile_to_lean) fn validate_store(
        &self,
        store: &StoreFactResult,
        expected: &Fact,
    ) -> Result<(), LeanCompileError> {
        let actual = match store {
            StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
            StoreFactResult::ForallFact(stored) => Fact::ForallFact(stored.fact.clone()),
            StoreFactResult::AndFact(stored) => Fact::AndFact(stored.fact.clone()),
            StoreFactResult::ChainFact(stored) => Fact::ChainFact(stored.fact.clone()),
            StoreFactResult::OrFact(_)
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
