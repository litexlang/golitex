use super::exec_stmt_result::ExecLetObjStmtResult;
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::execution_environment::LetObjectBinding;
use crate::new_pipeline::execute::execute_fact_stmt::{equal_fact_from_let, VerifyState};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // `let name = value`
    // 1. WD the RHS value object
    // 2. affect global env (binding + defining equality)
    pub(super) fn exec_let_obj(
        &mut self,
        let_stmt: &LetObjStmt,
    ) -> RuntimeResult<ExecLetObjStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };
        let value_well_defined =
            self.verify_obj_well_definedness(&let_stmt.value, verify_state)?;

        let equality_fact_id = self.ids.allocate_fact_id();
        let equal_fact = equal_fact_from_let(
            equality_fact_id,
            let_stmt.name.clone(),
            let_stmt.value.clone(),
            let_stmt.line_file.clone(),
        );

        self.top_exec_env_mut().store_let_binding(
            let_stmt.name.clone(),
            LetObjectBinding {
                value: let_stmt.value.clone(),
                equality_fact_id,
            },
        );
        self.top_exec_env_mut().store_native_equal_fact(equal_fact);

        Ok(ExecLetObjStmtResult {
            statement: let_stmt.clone(),
            value_well_defined,
            stored_fact_ids: vec![equality_fact_id],
        })
    }
}
