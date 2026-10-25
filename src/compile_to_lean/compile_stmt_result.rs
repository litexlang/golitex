use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_proof_block_stmt::ExecProofBlockStmtResult;
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
        if matches!(
            result,
            ExecStmtResult::Trust(_)
                | ExecStmtResult::Definition(ExecDefinitionStmtResult::Axiom(_))
        ) {
            return self.compile_assumption_statement(result, position, local);
        }
        match result {
            ExecStmtResult::Fact(result) => {
                self.compile_fact_statement(result, position, index, local)
            }
            ExecStmtResult::Definition(result) => {
                self.compile_definition_statement(result, position, index, local)
            }
            ExecStmtResult::Witness(result) => {
                self.compile_witness_statement(result, position, index, local)
            }
            ExecStmtResult::Trust(_) => unreachable!(),
            ExecStmtResult::By(result) => self.compile_by_statement(result, position, index, local),
            ExecStmtResult::Register(result) => {
                self.compile_register_statement(result, position, index, local)
            }
            ExecStmtResult::ReleaseAndExpand(result) => {
                self.compile_release_and_expand_statement(result, position, index, local)
            }
            ExecStmtResult::ProofBlock(result) => match result {
                ExecProofBlockStmtResult::Claim(claim) => {
                    self.compile_claim_statement(claim, position, index, local)
                }
                ExecProofBlockStmtResult::Sketch(proof) => {
                    self.compile_sketch_statement(proof, position, index, local)
                }
            },
            ExecStmtResult::Command(_) => Err(LeanCompileError::unsupported("Command")),
        }
    }
}
