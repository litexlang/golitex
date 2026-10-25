use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactSetMinusSplitResult;

impl LitexToLeanCompiler {
    pub(super) fn compile_set_minus_inference(
        &self,
        proof: &InferInFactSetMinusSplitResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(member)) = seed else {
            return Err(LeanCompileError::unsupported("SetMinusInference/Seed"));
        };
        let Obj::SetOperator(SetOperator::SetMinus(set)) = &member.set else {
            return Err(LeanCompileError::unsupported("SetMinusInference/Carrier"));
        };
        let singleton = match set.right.as_ref() {
            Obj::SetFormer(SetFormer::ListSet(p)) if p.list.len() == 1 => Some(p.list[0].as_ref()),
            _ => None,
        };
        if singleton.is_some() != proof.singleton_inequality.is_some() {
            return Err(LeanCompileError::unsupported(
                "SetMinusInference/SingletonCapture",
            ));
        }
        let stores = [&proof.base_membership, &proof.excluded_membership]
            .into_iter()
            .chain(proof.singleton_inequality.as_ref());
        let mut seen = vec![member.fact_id];
        let mut declarations = Vec::new();
        for (i, captured) in stores.enumerate() {
            let id = captured.primary_fact_id();
            if seen.contains(&id) {
                return Err(LeanCompileError::unsupported("SetMinusInference/Identity"));
            }
            seen.push(id);
            let prior = SourcePosition {
                before: position.before + i,
                ..*position
            };
            let fact = self.resolve_fact(id, &prior)?;
            let matches = match (&fact, i) {
                (Fact::AtomicFact(AtomicFact::InFact(p)), 0) => {
                    p.element.ir() == member.element.ir() && p.set.ir() == set.left.ir()
                }
                (Fact::AtomicFact(AtomicFact::NotInFact(p)), 1) => {
                    p.element.ir() == member.element.ir() && p.set.ir() == set.right.ir()
                }
                (Fact::AtomicFact(AtomicFact::NotEqualFact(p)), 2) => {
                    p.left.ir() == member.element.ir()
                        && singleton.is_some_and(|x| x.ir() == p.right.ir())
                }
                _ => false,
            };
            if !matches {
                return Err(LeanCompileError::unsupported("SetMinusInference/Subject"));
            }
            self.validate_store(&captured.store, &fact)?;
            let object = self.compile_object_reference(&member.set, &prior)?;
            let element = self.compile_object_reference(&member.element, &prior)?;
            let split = format!(
                "((Litex.inSetMinus_iff {element} _set.val.left _set.val.right).mp {})",
                compiled.1
            );
            let body = if i < 2 {
                format!("{split}.{}", i + 1)
            } else {
                format!("(fun _same => {split}.2 ((Litex.inInsert_iff {element} _set.val.right.val.element _set.val.right.val.tail _set.val.right.wd).mpr (Or.inl _same)))")
            };
            let term = format!("(let _set := {object}; {body})");
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::InferredStore(&captured.store),
                usize::MAX,
            );
            declarations.push(self.emit_internal_fact(
                &fact,
                &(self.fact_proposition(&fact, &formed)?, term),
                &formed,
            )?);
        }
        Ok(declarations)
    }
}
