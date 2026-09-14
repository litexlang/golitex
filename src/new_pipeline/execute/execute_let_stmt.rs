use super::exec_stmt_result::ExecLetObjStmtResult;
use crate::new_pipeline::ast::obj::Identifier;
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::exec_env::IdentifierDefinitionMemory;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // `let name = value`
    // 1. WD the RHS value object
    // 2. record identifier in definitions.identifiers; equality id goes in the result
    pub(super) fn exec_let_obj(
        &mut self,
        let_stmt: &LetObjStmt,
    ) -> RuntimeResult<ExecLetObjStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };
        let value_well_defined = self.verify_obj_well_definedness(&let_stmt.value, verify_state)?;

        let equality_fact_id = self.ids.allocate_fact_id();

        if self
            .top_exec_env()
            .definitions
            .identifiers
            .contains_key(&let_stmt.identifier_id)
        {
            return Err(RuntimeError::Invariant(format!(
                "identifier `{}` is already defined in this ExecEnv",
                let_stmt.name
            )));
        }
        self.top_exec_env_mut().definitions.identifiers.insert(
            let_stmt.identifier_id,
            IdentifierDefinitionMemory {
                identifier: Identifier {
                    name: let_stmt.name.clone(),
                    identifier_id: let_stmt.identifier_id,
                },
            },
        );

        Ok(ExecLetObjStmtResult {
            statement: let_stmt.clone(),
            value_well_defined,
            stored_fact_ids: vec![equality_fact_id],
        })
    }
}
