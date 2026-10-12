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
                self.validate_store(&success.store_and_infer_result.store, &source)?;
                self.compile_completed_fact_statement(
                    &source,
                    compiled,
                    &success.store_and_infer_result,
                    position,
                    index,
                    local,
                )
            }
            ExecFactStmtResult::Failed(_) => Err(LeanCompileError::new(
                "Fact/Failed",
                "A failed fact is not proof evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_completed_fact_statement(
        &self,
        source: &Fact,
        compiled: (String, String),
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        self.validate_store(&store.store, source)?;
        let declaration = self.emit_fact(source, compiled.clone(), index, local, position);
        let name = format!("h_{}", source.fact_id().value());
        let reference = if local {
            name
        } else {
            self.context_application(&name, position)
        };
        let complete = SourcePosition {
            before: 1,
            ..*position
        };
        let mut declarations = vec![declaration];
        declarations.extend(self.compile_stored_inferences(
            store,
            source,
            &(compiled.0, reference),
            &complete,
        )?);
        Ok(declarations.join("\n\n"))
    }
}
