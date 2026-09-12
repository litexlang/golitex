use super::exec_stmt_result::{ExecLetObjStmtResult, LetObjEffect, LetObjWellDefinedResult};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::execution_environment::LetObjectBinding;
use crate::new_pipeline::execute::execute_fact_stmt::equal_fact_from_let;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // `let name = value`
    // 1. well-defined gate
    // 2. affect global env (binding + defining equality)
    pub(super) fn exec_let_obj(
        &mut self,
        let_stmt: &LetObjStmt,
    ) -> RuntimeResult<ExecLetObjStmtResult> {
        let well_defined = self.exec_let_obj_well_defined(let_stmt)?;
        let effect = self.exec_let_obj_affect_env(let_stmt)?;
        Ok(ExecLetObjStmtResult {
            statement: let_stmt.clone(),
            well_defined,
            effect,
        })
    }

    fn exec_let_obj_well_defined(
        &mut self,
        let_stmt: &LetObjStmt,
    ) -> RuntimeResult<LetObjWellDefinedResult> {
        ensure_let_value_supported(&let_stmt.value)?;
        Ok(LetObjWellDefinedResult {})
    }

    fn exec_let_obj_affect_env(
        &mut self,
        let_stmt: &LetObjStmt,
    ) -> RuntimeResult<LetObjEffect> {
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

        Ok(LetObjEffect {
            stored_fact_ids: vec![equality_fact_id],
        })
    }
}

// Tracer WD gate: numbers and `+` of those (e.g. `2`, `1 + 2`).
fn ensure_let_value_supported(obj: &Obj) -> RuntimeResult<()> {
    match obj {
        Obj::Number(_) => Ok(()),
        Obj::Add(add) => {
            ensure_let_value_supported(add.left.as_ref())?;
            ensure_let_value_supported(add.right.as_ref())?;
            Ok(())
        }
        _ => Err(RuntimeError::Unsupported(
            "let value: only numbers and `+` are wired for the tracer".to_string(),
        )),
    }
}
