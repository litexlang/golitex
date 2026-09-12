use super::exec_stmt_result::{ExecLetObjStmtResult, LetObjEffect};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::execution_environment::LetObjectBinding;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // `let name = value`: check a minimal WD gate, allocate defining-equality FactId,
    // store the binding in the top ExecEnv, return the effect mirror.
    pub(super) fn exec_let_obj(
        &mut self,
        let_stmt: &LetObjStmt,
    ) -> RuntimeResult<ExecLetObjStmtResult> {
        ensure_let_value_supported(&let_stmt.value)?;

        let equality_fact_id = self.ids.allocate_fact_id();
        self.top_exec_env_mut().store_let_binding(
            let_stmt.name.clone(),
            LetObjectBinding {
                value: let_stmt.value.clone(),
                equality_fact_id,
            },
        );

        Ok(ExecLetObjStmtResult {
            statement: let_stmt.clone(),
            effect: LetObjEffect {
                stored_fact_ids: vec![equality_fact_id],
            },
        })
    }
}

// Tracer WD gate: only numeric literals and `+` of those (e.g. `2`, `1 + 2`).
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
