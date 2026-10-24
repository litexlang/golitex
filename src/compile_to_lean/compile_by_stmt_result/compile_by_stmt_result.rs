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
            ExecByStmtResult::Extension(result) => {
                self.compile_by_extension_result(result, position, index, local)
            }
            ExecByStmtResult::FnExtension(result) => {
                self.compile_by_fn_extension_result(result, position, index, local)
            }
            ExecByStmtResult::EnumerateFiniteSet(
                crate::execute::execute_by_stmt::ExecByEnumerateFiniteSetStmtResult::Success(p),
            ) => self.compile_by_enumeration(
                &p.goal_wd,
                &p.assignments,
                &p.stored,
                position,
                index,
                local,
            ),
            ExecByStmtResult::For(
                crate::execute::execute_by_stmt::ExecByForStmtResult::Success(p),
            ) => self.compile_by_enumeration(
                &p.goal_wd,
                &p.assignments,
                &p.stored,
                position,
                index,
                local,
            ),
            ExecByStmtResult::EnumerateFiniteSet(_) | ExecByStmtResult::For(_) => {
                Err(LeanCompileError::unsupported("Enumeration/Failed"))
            }
            ExecByStmtResult::StrongInduc(result) => {
                self.compile_by_strong_induc_result(result, position, index, local)
            }
        }
    }
}
