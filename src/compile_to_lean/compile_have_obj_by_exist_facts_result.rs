use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecHaveObjByExistFactsStmtResult;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_have_by_exist_statement(
        &self,
        result: &ExecHaveObjByExistFactsStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecHaveObjByExistFactsStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("HaveByExist/Failed"));
        };
        let ExistShapedFact::Exist(source) = &proof.verify_exist.fact else {
            return Err(LeanCompileError::unsupported("HaveByExist/SourceFamily"));
        };
        if source.typed_parameters != proof.statement.param_def
            || source.facts != proof.statement.facts
        {
            return Err(LeanCompileError::unsupported("HaveByExist/SourceSubject"));
        }
        // Runtime retains the synthesized existential's binder identities when
        // publishing the witnesses. They are bound only inside the proof above.
        let outputs: Vec<_> = proof
            .statement
            .param_def
            .groups
            .iter()
            .flat_map(|group| group.params.iter().cloned())
            .collect();
        let (proposition, evidence) =
            self.compile_verify_plain_exist_success(&proof.verify_exist, position)?;
        self.compile_obtain_elimination(
            source,
            &proof.verify_exist.well_defined_proof,
            &outputs,
            &proof.store_and_infer_result,
            &HashMap::new(),
            format!("(show {proposition} from {evidence})"),
            position,
            position,
            local,
        )
    }
}
