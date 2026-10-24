use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_define_obj_statement(
        &self,
        result: &ExecDefineObjStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecDefineObjStmtResult::LetObj(result) => {
                self.compile_let_result(result, position, local)
            }
            ExecDefineObjStmtResult::HaveObjEqual(result) => {
                self.compile_have_equal_result(result, position, local)
            }
            ExecDefineObjStmtResult::HaveObjInNonemptySet(result) => {
                self.compile_arbitrary_have_result(result, position, local)
            }
            ExecDefineObjStmtResult::ObtainObjFromExistFact(result) => {
                self.compile_obtain_exist_statement(result, position, local)
            }
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(result) => {
                self.compile_obtain_atomic_statement(result, position, local)
            }
            ExecDefineObjStmtResult::HaveObjByExistFacts(result) => {
                self.compile_have_by_exist_statement(result, position, local)
            }
            ExecDefineObjStmtResult::HaveByFnPreimage(result) => {
                self.compile_have_fn_preimage_statement(result, position, local)
            }
            ExecDefineObjStmtResult::HaveByReplacementAxiom(_) => {
                Err(LeanCompileError::unsupported("Definition/DefineObj"))
            }
        }
    }
}
