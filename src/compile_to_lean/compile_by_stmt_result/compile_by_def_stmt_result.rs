use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_def_result(
        &self,
        result: &ExecByDefStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let proof = match result {
            ExecByDefStmtResult::Success(proof) => proof,
            ExecByDefStmtResult::Failed(_) => {
                return Err(LeanCompileError::new(
                    "ByDef/Failed",
                    "A failed definition request is not proof evidence.",
                ))
            }
        };
        let source = source_subject(&proof.proof)?;
        let goal_wd = match &proof.goal_wd {
            VerifyFactWellDefinedResult::Success(wd) => wd,
            VerifyFactWellDefinedResult::Failed(_) => {
                return Err(LeanCompileError::new(
                    "ByDef/GoalWD",
                    "Successful definition replay has failed goal formation.",
                ))
            }
        };
        let goal_scope = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::ByDef(proof),
            before: 0,
        };
        self.compile_fact_wd(goal_wd, &source, &goal_scope)?;
        if !matches!(&proof.proof, VerifyFactResult::AtomicExceptEquality(result)
            if matches!(result.as_ref(), VerifyAtomicExceptEqualityFactResult::Success(success)
                if matches!(&success.searched_proof, AtomicExceptEqualityFactSearchedProof::ByDefinition(_))))
        {
            return Err(LeanCompileError::new(
                "ByDef/Route",
                "Explicit definition replay must retain its actual definition proof route.",
            ));
        }
        let scope = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::ByDef(proof),
            before: 1,
        };
        let compiled = self.compile_verify(&proof.proof, &scope)?;
        self.validate_store(&proof.stored, &source)?;
        self.compile_completed_fact_statement(
            &source,
            compiled,
            &proof.stored,
            position,
            index,
            local,
        )
    }
}
