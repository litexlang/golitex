use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_statement(
        &self,
        result: &ExecByStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecByStmtResult::Thm(result) => {
                self.compile_by_thm_result(result, position, index, local)
            }
            ExecByStmtResult::Def(result) => {
                self.compile_by_def_result(result, position, index, local)
            }
            ExecByStmtResult::Induc(result) => {
                self.compile_by_induc_result(result, position, index, local)
            }
            ExecByStmtResult::Cases(result) => {
                self.compile_by_cases_result(result, position, index, local)
            }
            ExecByStmtResult::Contra(result) => {
                self.compile_by_contra_result(result, position, index, local)
            }
            ExecByStmtResult::Extension(_)
            | ExecByStmtResult::FnExtension(_)
            | ExecByStmtResult::EnumerateFiniteSet(_)
            | ExecByStmtResult::For(_)
            | ExecByStmtResult::StrongInduc(_) => Err(LeanCompileError::unsupported("By")),
        }
    }
}
