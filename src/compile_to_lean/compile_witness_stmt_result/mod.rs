mod compile_witness_atomic_fact_result;
mod compile_witness_exist_fact_result;
mod compile_witness_nonempty_set_result;

use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_witness_stmt::{
    ExecWitnessAtomicFactStmtResult, ExecWitnessExistFactStmtResult,
    ExecWitnessNonemptySetStmtResult, ExecWitnessStmtResult,
};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_witness_statement(
        &self,
        result: &ExecWitnessStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecWitnessStmtResult::WitnessExistFact(ExecWitnessExistFactStmtResult::Success(
                proof,
            )) => self.compile_witness_exist_statement(proof, position, index, local),
            ExecWitnessStmtResult::WitnessExistFact(ExecWitnessExistFactStmtResult::Failed(_)) => {
                Err(LeanCompileError::new(
                    "Witness/Failed",
                    "A failed witness result is not proof evidence.",
                ))
            }
            ExecWitnessStmtResult::WitnessAtomicFact(ExecWitnessAtomicFactStmtResult::Success(
                proof,
            )) => self.compile_witness_atomic_statement(proof, position, index, local),
            ExecWitnessStmtResult::WitnessAtomicFact(ExecWitnessAtomicFactStmtResult::Failed(
                _,
            )) => Err(LeanCompileError::new(
                "Witness/Failed",
                "A failed predicate witness is not proof evidence.",
            )),
            ExecWitnessStmtResult::WitnessNonemptySet(
                ExecWitnessNonemptySetStmtResult::Success(proof),
            ) => self.compile_witness_nonempty_statement(proof, position, index, local),
            ExecWitnessStmtResult::WitnessNonemptySet(
                ExecWitnessNonemptySetStmtResult::Failed(_),
            ) => Err(LeanCompileError::unsupported("WitnessNonempty/Failed")),
        }
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/compile_to_lean/witness/tests.rs"]
mod witness_tests;
