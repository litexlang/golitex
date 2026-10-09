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
            ExecByStmtResult::Cases(_)
            | ExecByStmtResult::Contra(_)
            | ExecByStmtResult::Def(_)
            | ExecByStmtResult::Extension(_)
            | ExecByStmtResult::FnExtension(_)
            | ExecByStmtResult::EnumerateFiniteSet(_)
            | ExecByStmtResult::For(_)
            | ExecByStmtResult::Induc(_)
            | ExecByStmtResult::StrongInduc(_) => Err(LeanCompileError::unsupported("By")),
        }
    }
}
