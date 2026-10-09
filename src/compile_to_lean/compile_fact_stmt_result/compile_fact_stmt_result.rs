use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_fact_statement(
        &self,
        result: &ExecFactStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecFactStmtResult::Success(success) => {
                let compiled = self.compile_verify(&success.verify_result, position)?;
                let source = source_subject(&success.verify_result)?;
                self.validate_store(&success.store_and_infer_result, &source)?;
                Ok(self.emit_fact(&source, compiled, index, local, position))
            }
            ExecFactStmtResult::Failed(_) => Err(LeanCompileError::new(
                "Fact/Failed",
                "A failed fact is not proof evidence.",
            )),
        }
    }
}
