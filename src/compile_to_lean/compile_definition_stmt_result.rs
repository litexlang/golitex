use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_definition_statement(
        &self,
        result: &ExecDefinitionStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecDefinitionStmtResult::DefineObj(result) => {
                self.compile_define_obj_statement(result, position, local)
            }
            ExecDefinitionStmtResult::DefThm(result) => {
                if local {
                    return Err(LeanCompileError::unsupported("Definition"));
                }
                match result {
                    ExecDefThmStmtResult::Success(proof) => {
                        self.compile_named_theorem(proof, position, index)
                    }
                    ExecDefThmStmtResult::Failed(_) => Err(LeanCompileError::new(
                        "Theorem/Failed",
                        "Failed theorem is not proof evidence.",
                    )),
                }
            }
            ExecDefinitionStmtResult::DefProp(result) => {
                self.compile_def_prop_statement(result, position, index, local)
            }
            ExecDefinitionStmtResult::HaveFnEqual(result) => {
                self.compile_have_fn_equal_statement(result, position, index, local)
            }
            ExecDefinitionStmtResult::HaveFnEqualCaseByCase(_)
            | ExecDefinitionStmtResult::HaveFnByForallExistUnique(_)
            | ExecDefinitionStmtResult::HaveFnByInduc(_)
            | ExecDefinitionStmtResult::DefAbstractProp(_)
            | ExecDefinitionStmtResult::DefStruct(_)
            | ExecDefinitionStmtResult::DefTemplate(_)
            | ExecDefinitionStmtResult::DefAlgoByCases(_)
            | ExecDefinitionStmtResult::DefAlgoByInduc(_)
            | ExecDefinitionStmtResult::Axiom(_)
            | ExecDefinitionStmtResult::DefStrategy(_) => {
                Err(LeanCompileError::unsupported("Definition"))
            }
        }
    }
}
