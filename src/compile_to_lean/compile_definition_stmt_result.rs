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
            ExecDefinitionStmtResult::DefThm(result) => match result {
                ExecDefThmStmtResult::Success(proof) => {
                    self.compile_named_theorem(proof, position, index, local)
                }
                ExecDefThmStmtResult::Failed(_) => Err(LeanCompileError::new(
                    "Theorem/Failed",
                    "Failed theorem is not proof evidence.",
                )),
            },
            ExecDefinitionStmtResult::DefProp(result) => {
                self.compile_def_prop_statement(result, position, index, local)
            }
            ExecDefinitionStmtResult::HaveFnEqual(result) => {
                self.compile_have_fn_equal_statement(result, position, index, local)
            }
            ExecDefinitionStmtResult::HaveFnByInduc(result) => {
                self.compile_have_fn_by_induc_statement(result, position, index, local)
            }
            ExecDefinitionStmtResult::HaveFnByForallExistUnique(result) => {
                self.compile_have_fn_by_exist_statement(result, position, local)
            }
            ExecDefinitionStmtResult::HaveFnEqualCaseByCase(result) => {
                self.compile_have_fn_cases_statement(result, position, local)
            }
            ExecDefinitionStmtResult::DefAbstractProp(result) => {
                self.compile_abstract_prop_statement(result, index, local)
            }
            ExecDefinitionStmtResult::DefStruct(result) => {
                self.compile_struct_statement(result, position, index, local)
            }
            ExecDefinitionStmtResult::DefTemplate(result) => {
                self.compile_template_statement(result, position, local)
            }
            ExecDefinitionStmtResult::DefAlgoByCases(_)
            | ExecDefinitionStmtResult::DefAlgoByInduc(_)
            | ExecDefinitionStmtResult::Axiom(_)
            | ExecDefinitionStmtResult::DefStrategy(_) => {
                Err(LeanCompileError::unsupported("Definition"))
            }
        }
    }
}
