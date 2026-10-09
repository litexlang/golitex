use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_statement(
        &self,
        result: &ExecStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
    ) -> Result<String, LeanCompileError> {
        self.compile_statement_in_scope(result, position, index, false)
    }

    pub(in crate::compile_to_lean) fn compile_statement_in_scope(
        &self,
        result: &ExecStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let source_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::Statement(result),
            before: 0,
        };
        let position = &source_position;
        match result {
            ExecStmtResult::Fact(result) => {
                self.compile_fact_statement(result, position, index, local)
            }
            ExecStmtResult::Definition(result) => {
                self.compile_definition_statement(result, position, index, local)
            }
            ExecStmtResult::Witness(_) => Err(LeanCompileError::unsupported("Witness")),
            ExecStmtResult::Trust(_) => Err(LeanCompileError::unsupported("Trust")),
            ExecStmtResult::By(result) => self.compile_by_statement(result, position, index, local),
            ExecStmtResult::Register(_) => Err(LeanCompileError::unsupported("Register")),
            ExecStmtResult::ReleaseAndExpand(_) => {
                Err(LeanCompileError::unsupported("ReleaseAndExpand"))
            }
            ExecStmtResult::ProofBlock(_) => Err(LeanCompileError::unsupported("ProofBlock")),
            ExecStmtResult::Command(_) => Err(LeanCompileError::unsupported("Command")),
        }
    }
}
