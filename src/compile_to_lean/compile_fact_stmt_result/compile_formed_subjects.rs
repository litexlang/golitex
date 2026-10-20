use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Publish constructors whose original store registered a reusable WD id.
    pub(in crate::compile_to_lean) fn compile_formed_subjects(
        &self,
        verify: &VerifyFactResult,
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut declarations = Vec::new();
        for (index, subject) in store.formed_subjects.iter().enumerate() {
            if store.formed_subjects[..index].iter().any(|earlier| {
                earlier.argument_index >= subject.argument_index || earlier.wd_id == subject.wd_id
            }) {
                return Err(LeanCompileError::new(
                    "WD/Registration",
                    "Duplicate or reordered WD registrations.",
                ));
            }
            let Some(proof) = formed_subject_proof(verify, subject.argument_index)? else {
                continue;
            };
            if self.resolve_wd(subject.wd_id, position)?.ir() != proof.obj().ir() {
                return Err(LeanCompileError::new(
                    "WD/Registration",
                    "Registered WD id has another subject.",
                ));
            }
            let verify_position = SourcePosition::new(
                Some(position),
                SourceOwner::Verify(verify),
                subject.argument_index,
            );
            let atomic_position;
            let original = match verify {
                VerifyFactResult::AtomicExceptEquality(result) => {
                    let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_ref()
                    else {
                        unreachable!("formed_subject_proof checked success")
                    };
                    atomic_position = SourcePosition::new(
                        Some(&verify_position),
                        SourceOwner::AtomicWD(&result.well_defined_proof),
                        subject.argument_index,
                    );
                    &atomic_position
                }
                _ => &verify_position,
            };
            let value = self.compile_wd(proof, original)?;
            let name = format!("_object_w{}", subject.wd_id.value());
            declarations.push(if local {
                format!("let {name} := {value}")
            } else {
                format!(
                    "noncomputable def {name}{} := {value}",
                    self.context_header(position)?
                )
            });
        }
        Ok(declarations)
    }
}

pub(in crate::compile_to_lean) fn formed_subject_proof(
    verify: &VerifyFactResult,
    index: usize,
) -> Result<Option<&ObjWellDefinedProof>, LeanCompileError> {
    let proof = match verify {
        VerifyFactResult::Equality(result) => match result.as_ref() {
            VerifyEqualityResult::Success(result) => [
                &result.well_defined_proof.left,
                &result.well_defined_proof.right,
            ]
            .get(index)
            .copied(),
            _ => None,
        },
        VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(result) => result
                .well_defined_proof
                .well_defined_of_each_parameter
                .get(index),
            _ => None,
        },
        _ => None,
    }
    .ok_or_else(|| {
        LeanCompileError::new(
            "WD/Registration",
            "Registration has no original atomic argument WD.",
        )
    })?;
    // Leaves already have compact canonical constructors. Do not add aliases for them.
    Ok((!matches!(
        proof.obj(),
        Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
    ))
    .then_some(proof))
}
