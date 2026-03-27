use super::Runtime;
use crate::error::ExecStmtError;
use crate::infer::InferResult;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::definition_stmt::{DefStructWithFieldsStmt, DefStructWithNoFieldStmt};
use crate::stmt::Stmt;
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    pub fn def_struct_with_no_field_stmt(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.runtime_context.push_env();
        let result =
            self.def_struct_with_no_field_stmt_verify_process(def_struct_with_no_field_stmt);
        self.runtime_context.pop_env();

        if let Err(e) = result {
            return Err(ExecStmtError::new(
                Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                Some(e.into()),
                vec![],
            ));
        }

        self.store_def_struct_with_no_field(def_struct_with_no_field_stmt)?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ))
    }

    fn def_struct_with_no_field_stmt_verify_process(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<(), ExecStmtError> {
        let stmt_for_error = Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone());
        let verify_state = VerifyState::new(0, false);

        self.define_params_with_type(&def_struct_with_no_field_stmt.params_def_with_type, false)
            .map_err(|define_params_error| {
                ExecStmtError::new(
                    stmt_for_error.clone(),
                    Some(define_params_error.into()),
                    vec![],
                )
            })?;

        for dom_fact in def_struct_with_no_field_stmt.dom_facts.iter() {
            self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                dom_fact,
                &verify_state,
            )
            .map_err(|inner_exec_error| {
                ExecStmtError::new(
                    stmt_for_error.clone(),
                    Some(inner_exec_error.into()),
                    vec![],
                )
            })?;
        }

        self.verify_obj_well_defined_and_store_cache(
            &def_struct_with_no_field_stmt.equal_to,
            &verify_state,
        )
        .map_err(|well_defined_error| {
            ExecStmtError::new(stmt_for_error, Some(well_defined_error.into()), vec![])
        })?;

        Ok(())
    }

    pub fn def_struct_with_fields_stmt(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.runtime_context.push_env();
        let result = self.def_struct_with_fields_stmt_verify_process(def_struct_with_fields_stmt);
        self.runtime_context.pop_env();

        if let Err(e) = result {
            return Err(ExecStmtError::new(
                Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
                Some(e.into()),
                vec![],
            ));
        }

        self.store_def_struct_with_fields(def_struct_with_fields_stmt)
            .map_err(|e| {
                ExecStmtError::new(
                    Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
                    Some(e.into()),
                    vec![],
                )
            })?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ))
    }

    fn def_struct_with_fields_stmt_verify_process(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<(), ExecStmtError> {
        _ = def_struct_with_fields_stmt.params_def_with_type.clone();
        Ok(())
    }
}
