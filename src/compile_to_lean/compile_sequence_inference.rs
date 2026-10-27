use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

impl LitexToLeanCompiler {
    fn validate_sequence_inference(
        &self,
        source: &InFact,
        carrier: &Obj,
        store: &StoreFactResult,
    ) -> Result<(), LeanCompileError> {
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
        match carrier {
            Obj::SetFormer(SetFormer::FiniteSeqSet(sequence)) => {
                Self::validate_finite_seq_signature(sequence, signature)?
            }
            Obj::SetFormer(SetFormer::MatrixSet(matrix)) => {
                Self::validate_matrix_signature(matrix, signature)?
            }
            Obj::SetFormer(SetFormer::SeqSet(sequence)) => {
                Self::validate_seq_signature(sequence, signature)?
            }
            _ => return Err(LeanCompileError::unsupported("Sequence/InferenceSource")),
        }

        self.validate_store(store, &Fact::AtomicFact(stored.fact.clone()))
    }

    pub(in crate::compile_to_lean) fn compile_sequence_inference(
        &self,
        rule: &InferInFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(source)) = seed else {
            return Err(LeanCompileError::unsupported("FiniteSeq/InferenceSource"));
        };
        let canonical;
        let (derived, source_carrier, carrier_equal) = match rule {
            InferInFactResult::FiniteSeqExpand(p)
                if matches!(source.set, Obj::SetFormer(SetFormer::FiniteSeqSet(_))) =>
            {
                (&p.derived, &source.set, None)
            }
            InferInFactResult::SeqExpand(p)
                if matches!(source.set, Obj::SetFormer(SetFormer::SeqSet(_))) =>
            {
                (&p.derived, &source.set, None)
            }
            InferInFactResult::MatrixExpand(p) if p.source_fact_id == source.fact_id => {
                canonical = Obj::SetFormer(SetFormer::MatrixSet(p.matrix_space.clone()));
                (&p.derived, &canonical, Some(&p.carrier_equal))
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FunctionSpace/InferenceSource",
                ))
            }
        };
        let store = &derived.store;
        self.validate_sequence_inference(source, source_carrier, store)?;
        let fact = self.resolve_fact(store.primary_fact_id(), position)?;
        self.validate_store(store, &fact)?;
        let carrier = self.compile_object_reference(source_carrier, position)?;
        let original_carrier = self.compile_object_reference(&source.set, position)?;
        let source_same = carrier_equal
            .map(|path| self.compile_equality_path(&source.set, source_carrier, path, position))
            .transpose()?;
        let receiver = self.compile_object_reference(&source.element, position)?;
        let name = format!("_object_h{}", store.primary_fact_id().value());
        let (signature, equality) = match source_carrier {
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => (
                format!("(Litex.finiteSeqSignature {carrier})"),
                "finiteSeq_eq_fnSet",
            ),
            Obj::SetFormer(SetFormer::MatrixSet(_)) => (
                format!("(Litex.matrixSignature {carrier})"),
                "matrixSet_eq_fnSet",
            ),
            Obj::SetFormer(SetFormer::SeqSet(_)) => (
                format!("(Litex.seqSignature {carrier}.val.carrier)"),
                "seqSet_eq_fnSet",
            ),
            _ => return Err(LeanCompileError::unsupported("Sequence/InferenceSource")),
        };
        let constructor = format!("(Litex.fnSet {signature})");
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
        let carrier_same = format!("(Litex.{equality} {carrier})");
        let carrier_same = if let Some(same) = source_same {
            format!("({same}.trans {carrier_same})")
        } else {
            carrier_same
        };
        let term = format!("(Litex.inOfSame {receiver} {receiver} {original_carrier} {reference} (Litex.sameRefl {receiver}) {carrier_same} {})", compiled.1);
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
    pub(in crate::compile_to_lean) fn compile_sequence_inferred_subject(
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
                    let captured = match rule {
                        InferInFactResult::FiniteSeqExpand(proof) => &proof.derived,
                        InferInFactResult::MatrixExpand(proof) => &proof.derived,
                        InferInFactResult::SeqExpand(proof) => &proof.derived,
                        _ => continue,
                    };
                    if captured.primary_fact_id() != store.primary_fact_id() {
                        continue;
                    }
                    let canonical = if let InferInFactResult::MatrixExpand(proof) = rule {
                        Obj::SetFormer(SetFormer::MatrixSet(proof.matrix_space.clone()))
                    } else {
                        source.set.clone()
                    };
                    self.validate_sequence_inference(source, &canonical, store)?;
                    self.validate_store(&captured.store, &Fact::AtomicFact(stored.fact.clone()))?;
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
