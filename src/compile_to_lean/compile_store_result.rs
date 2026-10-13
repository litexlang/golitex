use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactResult;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferResult};

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
            Some(InferResult::AtomicFact(infer)) => {
                self.validate_store(&store.store, seed)?;
                let current = SourcePosition::new(
                    Some(position),
                    SourceOwner::AtomicInference(seed, infer),
                    0,
                );
                self.compile_atomic_inferences(infer, seed, compiled, &current)
            }
            Some(InferResult::AndFact(_)) | Some(InferResult::ChainFact(_)) => {
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
            Some(InferResult::AtomicFact(infer @ InferAtomicFactResult::InFact(rules))) => {
                (infer, rules)
            }
            _ => return Ok(declarations),
        };
        for (index, rule) in rules.iter().enumerate() {
            if let InferInFactResult::SignedStandardSetSign(sign) = rule {
                // Builder projections precede the sign rule in this original
                // membership dispatcher. Keep the sign's own WD/store pending.
                let completed = rules[..index]
                    .iter()
                    .filter_map(|rule| match rule {
                        InferInFactResult::SetBuilder(proof) => Some(proof),
                        _ => None,
                    })
                    .flat_map(|proof| &proof.steps)
                    .map(|step| step.projections.len())
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
            Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) => rules,
            _ => return Ok(Vec::new()),
        };
        let mut declarations = Vec::new();
        for rule in rules {
            if let InferInFactResult::SetBuilder(proof) = rule {
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
        if matches!(member_fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.set == Obj::StandardSet(StandardSet::RPos))
        {
            return self.compile_positive_real_sign_inference(sign, member_fact, member, position);
        }
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
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::InferredStore(&captured.store),
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

    fn compile_positive_real_sign_inference(
        &self,
        sign: &crate::store_fact_and_infer::InferInFactSignedStandardSetSignResult,
        member_fact: &Fact,
        member: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(source)) = member_fact else {
            return Err(LeanCompileError::unsupported(
                "Inference/PositiveRealFamily",
            ));
        };
        if source.set != Obj::StandardSet(StandardSet::RPos) || sign.derived.len() != 3 {
            return Err(LeanCompileError::new(
                "Inference/PositiveRealArity",
                "Positive-real membership needs its three actual ordered sign stores.",
            ));
        }
        let mut declarations = Vec::new();
        let mut ids = std::collections::HashSet::new();
        for (index, captured) in sign.derived.iter().enumerate() {
            let prior = SourcePosition {
                before: position.before + index,
                ..*position
            };
            let fact = self.resolve_fact(captured.primary_fact_id(), &prior)?;
            if !ids.insert(captured.primary_fact_id()) {
                return Err(LeanCompileError::new(
                    "Inference/PositiveRealIdentity",
                    "Positive-real projections require distinct stored identities.",
                ));
            }
            let subject_matches = match (index, &fact) {
                (0, Fact::AtomicFact(AtomicFact::LessFact(f))) => {
                    is_exact_zero(&f.left) && f.right.ir() == source.element.ir()
                }
                (1, Fact::AtomicFact(AtomicFact::LessEqualFact(f))) => {
                    is_exact_zero(&f.left) && f.right.ir() == source.element.ir()
                }
                (2, Fact::AtomicFact(AtomicFact::NotEqualFact(f))) => {
                    f.left.ir() == source.element.ir() && is_exact_zero(&f.right)
                }
                _ => false,
            };
            if !subject_matches {
                return Err(LeanCompileError::new(
                    "Inference/PositiveRealSubject",
                    "The ordered positive-real store has another predicate or endpoint.",
                ));
            }
            self.validate_store(&captured.store, &fact)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            let object = self.compile_object_reference(&source.element, &formed)?;
            let strict = format!("h_{}", sign.derived[0].primary_fact_id().value());
            let proof = match index {
                0 => format!("(Litex.inRPos_positive {object} {})", member.1),
                1 => format!("(Litex.ltToLe (Litex.number (M := M) 0) {object} {strict})"),
                2 => format!("(fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) {object} {strict}) _litex_zero.symm)"),
                _ => unreachable!(),
            };
            let compiled = (self.fact_proposition(&fact, &formed)?, proof);
            declarations.push(self.emit_internal_fact(&fact, &compiled, &formed));
        }
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
            StoreFactResult::OrFact(stored) => Fact::OrFact(stored.fact.clone()),
            StoreFactResult::ExistShapedFact(_)
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
