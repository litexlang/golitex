use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_seq_equality(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (source, sequence, signature, reversed) = match (&fact.left, &fact.right) {
            (
                a @ Obj::SetFormer(SetFormer::SeqSet(s)),
                Obj::FunctionSpace(FunctionSpace::FnSet(f)),
            ) => (a, s, f, false),
            (
                Obj::FunctionSpace(FunctionSpace::FnSet(f)),
                a @ Obj::SetFormer(SetFormer::SeqSet(s)),
            ) => (a, s, f, true),
            _ => return Err(LeanCompileError::unsupported("Seq/EqualitySubject")),
        };
        Self::validate_seq_signature(sequence, signature)?;
        let source = self.compile_object_reference(source, position)?;
        let proof = format!("(Litex.seqSet_eq_fnSet {source})");
        Ok(if reversed {
            format!("{proof}.symm")
        } else {
            proof
        })
    }
}
