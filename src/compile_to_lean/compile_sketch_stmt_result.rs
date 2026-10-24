use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_proof_block_stmt::ExecSketchStmtResult;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_sketch_statement(
        &self,
        result: &ExecSketchStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecSketchStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::new(
                "Sketch/Failed",
                "A failed sketch is not proof evidence.",
            ));
        };
        let scope = SourcePosition::new(Some(position), SourceOwner::Sketch(proof), 0);
        let mut body = Vec::new();
        for (index, step) in proof.proof_steps.iter().enumerate() {
            body.push(self.compile_statement_in_scope(
                step,
                &SourcePosition {
                    before: index,
                    ..scope
                },
                index + 1,
                true,
            )?);
        }
        // Elaborate every original child, then discard its lexical context.
        // This marker has no source FactId and publishes no source conclusion.
        body.push("exact True.intro".to_string());
        let declaration = if local {
            "have : True".to_string()
        } else {
            format!(
                "include M in\nprivate theorem _sketch_{index}{} : True",
                self.context_header(position)?
            )
        };
        Ok(format!(
            "{declaration} := by\n  {}",
            body.join("\n").replace('\n', "\n  ")
        ))
    }
}
