use super::Runtime;
use crate::error::ExecStmtError;
use crate::fact::{AtomicFact, Fact, InFact};
use crate::infer::InferResult;
use crate::obj::{FieldAccess, Identifier, Obj};
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use crate::stmt::definition_stmt::{DefStructWithFieldsStmt, DefStructWithNoFieldStmt};
use crate::stmt::Stmt;
use crate::verify::VerifyState;

impl Runtime {
    pub fn def_struct_with_no_field_stmt(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.push_env();
        let result =
            self.def_struct_with_no_field_stmt_verify_process(def_struct_with_no_field_stmt);
        self.pop_env();

        if let Err(e) = result {
            return Err(ExecStmtError::new(
                Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                "".to_string(),
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
                    "".to_string(),
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
                    "".to_string(),
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
            ExecStmtError::new(
                stmt_for_error,
                "".to_string(),
                Some(well_defined_error.into()),
                vec![],
            )
        })?;

        Ok(())
    }

    pub fn def_struct_with_fields_stmt(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        self.push_env();
        let result = self.def_struct_with_fields_stmt_verify_process(def_struct_with_fields_stmt);
        self.pop_env();

        if let Err(e) = result {
            return Err(ExecStmtError::new(
                Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
                "".to_string(),
                Some(e.into()),
                vec![],
            ));
        }

        self.store_def_struct_with_fields(def_struct_with_fields_stmt)
            .map_err(|e| {
                ExecStmtError::new(
                    Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
                    "".to_string(),
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
        let stmt_for_error = Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone());
        let verify_state = VerifyState::new(0, false);

        self.define_params_with_type(&def_struct_with_fields_stmt.params_def_with_type, false)
            .map_err(|define_params_error| {
                ExecStmtError::new(
                    stmt_for_error.clone(),
                    "".to_string(),
                    Some(define_params_error.into()),
                    vec![],
                )
            })?;

        for (_, field_type_obj) in def_struct_with_fields_stmt.fields.iter() {
            self.verify_obj_well_defined_and_store_cache(field_type_obj, &verify_state)
                .map_err(|well_defined_error| {
                    ExecStmtError::new(
                        stmt_for_error.clone(),
                        "".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    )
                })?;
        }
        // 这些 field 的名字不能重复
        for (i, (field_name, _)) in def_struct_with_fields_stmt.fields.iter().enumerate() {
            for (j, (other_field_name, _)) in def_struct_with_fields_stmt.fields.iter().enumerate()
            {
                if i != j && field_name == other_field_name {
                    return Err(ExecStmtError::with_message_and_cause(
                        stmt_for_error.clone(),
                        format!(
                            "def_struct_with_fields_stmt: duplicated field name `{}`",
                            field_name
                        ),
                        None,
                        vec![],
                    ));
                }
            }
        }

        for (field_name, field_type_obj) in def_struct_with_fields_stmt.fields.iter() {
            let identifier_with_field = FieldAccess::new(
                def_struct_with_fields_stmt.name.clone(),
                vec![field_name.clone()],
            );

            self.store_identifier_obj(&identifier_with_field.to_string())?;

            let identifier_in_field_type_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(identifier_with_field.to_string())),
                field_type_obj.clone(),
                def_struct_with_fields_stmt.line_file,
            )));

            self.store_fact_without_well_defined_verified_and_infer(&identifier_in_field_type_fact)
                .map_err(|store_fact_error| {
                    ExecStmtError::new(
                        stmt_for_error.clone(),
                        "".to_string(),
                        Some(store_fact_error.into()),
                        vec![],
                    )
                })?;
        }

        for struct_equiv_fact in def_struct_with_fields_stmt.facts.iter() {
            self.verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                struct_equiv_fact,
                &verify_state,
            )
            .map_err(|inner_exec_error| {
                ExecStmtError::new(
                    stmt_for_error.clone(),
                    "".to_string(),
                    Some(inner_exec_error.into()),
                    vec![],
                )
            })?;
        }

        Ok(())
    }
}
