use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl<'a> LitexToLeanCompiler<'a> {
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
            VerifyFactResult::AndFact(_) => Err(LeanCompileError::unsupported("AndFact")),
            VerifyFactResult::ChainFact(_) => Err(LeanCompileError::unsupported("ChainFact")),
            VerifyFactResult::OrFact(_) => Err(LeanCompileError::unsupported("OrFact")),
            VerifyFactResult::ExistShapedFact(_) => {
                Err(LeanCompileError::unsupported("ExistShapedFact"))
            }
            VerifyFactResult::ForallFactWithIff(_) => {
                Err(LeanCompileError::unsupported("ForallFactWithIff"))
            }
            VerifyFactResult::NotForall(_) => Err(LeanCompileError::unsupported("NotForall")),
        }
    }
}
