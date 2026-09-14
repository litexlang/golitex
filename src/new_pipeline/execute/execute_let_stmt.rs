use super::exec_stmt_result::ExecLetObjStmtResult;
use crate::new_pipeline::ast::fact::{EqualFact, Fact};
use crate::new_pipeline::ast::obj::{AtomObj, Identifier, Obj};
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // `let name = value`
    // 1. WD the RHS value object
    // 2. bind the identifier
    // 3. store `name = value` into known equality (and facts_by_id)
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

        if self
            .top_exec_env()
            .definitions
            .identifiers
            .contains_key(&let_stmt.name)
        {
            return Err(RuntimeError::Invariant(format!(
                "identifier `{}` is already defined in this ExecEnv",
                let_stmt.name
            )));
        }
        self.top_exec_env_mut().definitions.identifiers.insert(
            let_stmt.name.clone(),
            DefinedIdentifierInfo {
                identifier: Identifier::new(let_stmt.name.clone()),
            },
        );

        let equality_fact_id = self.ids.allocate_fact_id();
        let left = Obj::Atom(AtomObj::Identifier(Identifier::new(let_stmt.name.clone())));
        let equal_fact: Fact = EqualFact {
            fact_id: equality_fact_id,
            left,
            right: let_stmt.value.clone(),
            line_file: Some(let_stmt.line_file.clone()),
        }
        .into();
        let store_and_infer_result = self.store_fact_and_infer(&equal_fact)?;

        Ok(ExecLetObjStmtResult {
            statement: let_stmt.clone(),
            value_well_defined,
            stored_fact_ids: store_and_infer_result.stored_fact_ids,
        })
    }
}
