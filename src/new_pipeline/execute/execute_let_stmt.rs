use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
use crate::new_pipeline::execute::execute_fact_stmt::{VerifyObjWellDefinedResult, VerifyState};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};
use std::rc::Rc;

// Pipeline: WD the RHS value → affect global env. No local env.
pub struct ExecLetObjStmtSuccessResult {
    pub statement: LetObjStmt,
    pub value_well_defined: VerifyObjWellDefinedResult,
    pub stored_fact_ids: Vec<FactId>,
}

pub enum ExecLetObjStmtResult {
    Success(ExecLetObjStmtSuccessResult),
    Failed(VerifyObjWellDefinedResult),
}

impl ExecLetObjStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

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
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };
        let value_well_defined = self.verify_obj_well_definedness(&let_stmt.value, verify_state)?;
        if value_well_defined.is_failed() {
            return Ok(ExecLetObjStmtResult::Failed(value_well_defined));
        }

        if self.identifier_defined_in_stack(&let_stmt.name.name) {
            return Err(RuntimeError::InternalBug(format!(
                "identifier `{}` is already defined in this ExecEnv",
                let_stmt.name.name
            )));
        }
        self.top_exec_env_mut().definitions.identifiers.insert(
            let_stmt.name.name.clone(),
            StoredIdentifierDefinition::LetObj((
                let_stmt.name.name.clone(),
                Rc::new(let_stmt.clone()),
            )),
        );

        let equality_fact_id = self.ids.allocate_fact_id();
        // Definition key stays plain; stored equality LHS uses global name at file root.
        let left = Obj::Identifier(self.identifier_obj_for_stored_mention(&let_stmt.name));
        let equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: equality_fact_id,
            left,
            right: let_stmt.value.clone(),
            line_file: Some(let_stmt.line_file.clone()),
        }));
        let store_and_infer_result = self.store_fact_and_infer(&equal_fact)?;

        Ok(ExecLetObjStmtResult::Success(ExecLetObjStmtSuccessResult {
            statement: let_stmt.clone(),
            value_well_defined,
            stored_fact_ids: store_and_infer_result.stored_fact_ids(),
        }))
    }
}
