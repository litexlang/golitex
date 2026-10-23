use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify(
        &self,
        result: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::Verify(result),
            before: 0,
        };
        let position = &source_position;
        match result {
            VerifyFactResult::Equality(result) => {
                self.compile_verify_equality_result(result, position)
            }
            VerifyFactResult::AtomicExceptEquality(result) => {
                self.compile_verify_atomic_except_equality_result(result, position)
            }
            VerifyFactResult::ForallFact(result) => {
                self.compile_verify_forall_result(result, position)
            }
            VerifyFactResult::AndFact(result) => self.compile_verify_and_result(result, position),
            VerifyFactResult::ChainFact(result) => {
                self.compile_verify_chain_result(result, position)
            }
            VerifyFactResult::OrFact(result) => self.compile_verify_or_result(result, position),
            VerifyFactResult::ExistShapedFact(result) => {
                self.compile_verify_exist_result(result, position)
            }
            VerifyFactResult::ForallFactWithIff(result) => {
                self.compile_verify_forall_iff(result, position)
            }
            VerifyFactResult::NotForall(_) => Err(LeanCompileError::unsupported("NotForall")),
        }
    }
}
