//! Sketch statement compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_sketch_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessSketchStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("a `sketch` unexpectedly exported facts to its parent environment".into());
        }
        let proof = result.proof.as_ref().ok_or_else(|| {
            "a successful `sketch` retained no recursive proof result".to_string()
        })?;
        if !proof.proof_scope.assumption_infers.is_empty()
            || !proof.proof_scope.assumption_components.is_empty()
        {
            return Err("a `sketch` retained unexpected local assumptions".into());
        }
        if proof.proof_steps.len() != result.statement.proof.len() {
            return Err("a `sketch` result changed its source proof-step order".into());
        }

        let nested_declarations =
            self.compile_stmt_results_in_new_local_environment(&proof.proof_steps)?;
        self.next_sketch_namespace_index += 1;
        let namespace = format!("__Sketch{:02}", self.next_sketch_namespace_index);
        self.declarations.push(format!(
            "namespace {namespace}\n\n{}\n\nend {namespace}",
            nested_declarations.join("\n\n")
        ));
        Ok(())
    }
}
