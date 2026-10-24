use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferInFactFiniteSeqExpandResult, InferInFactResult, InferResult,
};

impl LitexToLeanCompiler {
    fn validate_finite_seq_inference(
        &self,
        source: &InFact,
        store: &StoreFactResult,
    ) -> Result<(), LeanCompileError> {
        let Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) = &source.set else {
            return Err(LeanCompileError::unsupported("FiniteSeq/InferenceSource"));
        };
        let StoreFactResult::AtomicFact(stored) = store else {
            return Err(LeanCompileError::unsupported("FiniteSeq/InferenceStore"));
        };
        let AtomicFact::InFact(derived) = &stored.fact else {
            return Err(LeanCompileError::unsupported(
                "FiniteSeq/InferenceConclusion",
            ));
        };
        if derived.element.ir() != source.element.ir() || derived.fact_id == source.fact_id {
            return Err(LeanCompileError::unsupported("FiniteSeq/InferenceSubject"));
        }
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &derived.set else {
            return Err(LeanCompileError::unsupported(
                "FiniteSeq/InferenceSignature",
            ));
        };
        Self::validate_finite_seq_signature(sequence, signature)?;
        self.validate_store(store, &Fact::AtomicFact(stored.fact.clone()))
    }

    pub(in crate::compile_to_lean) fn compile_finite_seq_inference(
        &self,
        proof: &InferInFactFiniteSeqExpandResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(source)) = seed else {
            return Err(LeanCompileError::unsupported("FiniteSeq/InferenceSource"));
        };
        let store = &proof.derived.store;
        self.validate_finite_seq_inference(source, store)?;
        let fact = self.resolve_fact(store.primary_fact_id(), position)?;
        self.validate_store(store, &fact)?;
        let carrier = self.compile_object_reference(&source.set, position)?;
        let receiver = self.compile_object_reference(&source.element, position)?;
        let name = format!("_object_h{}", store.primary_fact_id().value());
        let constructor = format!("(Litex.fnSet (Litex.finiteSeqSignature {carrier}))");
        let declaration = if position.is_local() {
            format!("let {name} := {constructor}")
        } else {
            format!(
                "noncomputable def {name}{} := {constructor}",
                self.context_header(position)?
            )
        };
        let reference = if position.is_local() {
            name
        } else {
            self.context_application(&name, position)
        };
        let term = format!("(Litex.inOfSame {receiver} {receiver} {carrier} {reference} (Litex.sameRefl {receiver}) (Litex.finiteSeq_eq_fnSet {carrier}) {})", compiled.1);
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::InferredStore(store),
            usize::MAX,
        );
        let conclusion = (format!("Litex.In {receiver} {reference}"), term);
        Ok(vec![
            declaration,
            self.emit_internal_fact(&fact, &conclusion, &formed)?,
        ])
    }

    /// Reuse only the function-set constructor belonging to this exact stored
    /// expansion. Its source sequence already carries the formation evidence.
    pub(in crate::compile_to_lean) fn compile_finite_seq_inferred_subject(
        &self,
        object: &Obj,
        store: &StoreFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let StoreFactResult::AtomicFact(stored) = store else {
            return Ok(None);
        };
        let AtomicFact::InFact(derived) = &stored.fact else {
            return Ok(None);
        };
        if derived.set != *object {
            return Ok(None);
        }
        let mut current = Some(position);
        while let Some(cursor) = current {
            let inference = match cursor.owner {
                SourceOwner::AtomicInference(
                    Fact::AtomicFact(AtomicFact::InFact(source)),
                    InferAtomicFactResult::InFact(rules),
                ) => Some((source, rules)),
                SourceOwner::PropInference(captured) => match (&captured.store, &captured.infer) {
                    (
                        StoreFactResult::AtomicFact(seed),
                        Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))),
                    ) => match &seed.fact {
                        AtomicFact::InFact(source) => Some((source, rules)),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            if let Some((source, rules)) = inference {
                for rule in rules {
                    let InferInFactResult::FiniteSeqExpand(proof) = rule else {
                        continue;
                    };
                    if proof.derived.primary_fact_id() != store.primary_fact_id() {
                        continue;
                    }
                    self.validate_finite_seq_inference(source, store)?;
                    self.validate_store(
                        &proof.derived.store,
                        &Fact::AtomicFact(stored.fact.clone()),
                    )?;
                    let name = format!("_object_h{}", store.primary_fact_id().value());
                    return Ok(Some(if cursor.is_local() {
                        name
                    } else {
                        self.context_application(&name, cursor)
                    }));
                }
            }
            current = cursor.parent;
        }
        Ok(None)
    }
}
