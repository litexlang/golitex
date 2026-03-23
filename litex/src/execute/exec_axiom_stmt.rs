use super::Runtime;
use crate::error::{ExecStmtError, StmtError};
use crate::fact::{Fact, OrFact};
use crate::infer::InferResult;
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use crate::stmt::axiom_stmt::{
    ByCartDefAxiomStmt, ByCasesAxiomStmt, ByContraAxiomStmt, ByExtensionAxiomStmt,
    ByFnDefAxiomStmt, ByInducAxiomStmt, EnumerateAxiomStmt, ForAxiomStmt,
};
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    fn exec_by_cases_axiom_stmt_verify_cases_cover_all_situations(
        &mut self,
        stmt: &ByCasesAxiomStmt,
    ) -> Result<(), ExecStmtError> {
        let all_cases_or_fact = Fact::OrFact(OrFact::new(stmt.cases.clone(), stmt.line_file));
        self.verify_fact_return_err_if_not_true(&all_cases_or_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                ExecStmtError::new(
                    stmt.stmt_type_name(),
                    "by_cases: cannot verify that all cases cover all situations".to_string(),
                    Some(verify_error.into()),
                    stmt.line_file,
                )
            })?;
        Ok(())
    }

    fn exec_by_cases_axiom_stmt_prove_then_facts_under_case(
        &mut self,
        stmt: &ByCasesAxiomStmt,
        case_index: usize,
        inside_results: &mut Vec<NonErrStmtExecResult>,
    ) -> Result<(), ExecStmtError> {
        for then_fact in stmt.then_facts.iter() {
            let exec_fact_result = self.exec_fact(then_fact).map_err(|statement_error| {
                ExecStmtError::new_with_inside_results(
                    stmt.stmt_type_name(),
                    format!(
                        "by_cases: failed to prove `{}` under case `{}`",
                        then_fact, stmt.cases[case_index]
                    ),
                    Some(statement_error),
                    std::mem::take(inside_results),
                    stmt.line_file,
                )
            })?;
            inside_results.push(exec_fact_result);
        }
        Ok(())
    }

    fn exec_by_cases_axiom_stmt_for_one_case(
        &mut self,
        stmt: &ByCasesAxiomStmt,
        case_index: usize,
    ) -> Result<Vec<NonErrStmtExecResult>, ExecStmtError> {
        let case_fact = &stmt.cases[case_index];
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();

        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
            &case_fact.to_exist_or_and_chain_atomic_fact(),
        )
        .map_err(|store_fact_error| {
            ExecStmtError::new(
                stmt.stmt_type_name(),
                format!("by_cases: failed to assume case `{}`", case_fact),
                Some(store_fact_error.into()),
                stmt.line_file,
            )
        })?;

        for proof_stmt in stmt.proofs[case_index].iter() {
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(ExecStmtError::new_with_inside_results(
                        stmt.stmt_type_name(),
                        format!(
                            "by_cases: failed while executing proof under case `{}`",
                            case_fact
                        ),
                        Some(statement_error),
                        inside_results,
                        stmt.line_file,
                    ));
                }
            }
        }

        if let Some(impossible_fact) = &stmt.impossible_facts[case_index] {
            let verify_state = VerifyState::new(0, false);
            self.verify_exist_or_and_chain_atomic_fact(impossible_fact, &verify_state)
                .map_err(|verify_error| {
                    ExecStmtError::new(
                        stmt.stmt_type_name(),
                        format!(
                            "by_cases: failed to verify impossible fact `{}` under case `{}`",
                            impossible_fact, case_fact
                        ),
                        Some(verify_error.into()),
                        stmt.line_file,
                    )
                })?;

            return Ok(inside_results);
        }

        self.exec_by_cases_axiom_stmt_prove_then_facts_under_case(
            stmt,
            case_index,
            &mut inside_results,
        )?;
        Ok(inside_results)
    }

    pub fn exec_by_cases_axiom_stmt(
        &mut self,
        stmt: &ByCasesAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        self.exec_by_cases_axiom_stmt_verify_cases_cover_all_situations(stmt)
            .map_err(StmtError::from)?;

        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for case_index in 0..stmt.cases.len() {
            self.runtime_context.push_env();
            let one_case_result = self.exec_by_cases_axiom_stmt_for_one_case(stmt, case_index);
            self.runtime_context.pop_env();

            match one_case_result {
                Ok(mut one_case_inside_results) => {
                    inside_results.append(&mut one_case_inside_results);
                }
                Err(exec_stmt_error) => {
                    return Err(StmtError::ExecError(exec_stmt_error));
                }
            }
        }

        let mut infer_result = InferResult::new();
        for then_fact in stmt.then_facts.iter() {
            let one_then_fact_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(then_fact)
                .map_err(|store_fact_error| {
                    StmtError::ExecError(ExecStmtError::new(
                        stmt.stmt_type_name(),
                        format!("by_cases: failed to release `{}`", then_fact),
                        Some(store_fact_error.into()),
                        stmt.line_file,
                    ))
                })?;
            infer_result.append(one_then_fact_infer_result);
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                stmt.to_string(),
                infer_result,
                inside_results,
                stmt.line_file,
            ),
        ))
    }

    pub fn exec_by_contra_axiom_stmt(
        &mut self,
        stmt: &ByContraAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_enumerate_axiom_stmt(
        &mut self,
        stmt: &EnumerateAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_induc_axiom_stmt(
        &mut self,
        stmt: &ByInducAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_for_axiom_stmt(
        &mut self,
        stmt: &ForAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_extension_axiom_stmt(
        &mut self,
        stmt: &ByExtensionAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_fn_def_axiom_stmt(
        &mut self,
        stmt: &ByFnDefAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_by_cart_def_axiom_stmt(
        &mut self,
        stmt: &ByCartDefAxiomStmt,
    ) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }
}
