//! `have x S: facts` — prove synthesized exist, then introduce witnesses.
//!
//! Example:
//!   have left_greater R:
//!       left_greater > 100

use crate::new_pipeline::ast::fact::{ExistShapedFact, PlainExistFact};
use crate::new_pipeline::ast::stmt::HaveObjByExistFactsStmt;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyExistShapedFactFailed, VerifyExistShapedFactResult, VerifyFactResult, VerifyPlainExistFactResult,
    VerifyPlainExistFactSuccess, VerifyState,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::new_pipeline::execute::introduce_typed_parameters::SharedHaveDefinition;
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::rc::Rc;

pub enum ExecHaveObjByExistFactsStmtFailed {
    Exist(VerifyExistShapedFactFailed),
}

// Pipeline: synthesize exist → verify exist → define params + store body facts.
pub struct ExecHaveObjByExistFactsStmtSuccessResult {
    pub statement: HaveObjByExistFactsStmt,
    pub verify_exist: VerifyPlainExistFactSuccess,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
}

pub enum ExecHaveObjByExistFactsStmtResult {
    Success(ExecHaveObjByExistFactsStmtSuccessResult),
    Failed(ExecHaveObjByExistFactsStmtFailed),
}

impl ExecHaveObjByExistFactsStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Mathematical contract: the synthesized `exist` must be proved; then each
    // parameter becomes a fresh object and the body facts are stored.
    pub(super) fn exec_have_obj_by_exist_facts_stmt(
        &mut self,
        stmt: &HaveObjByExistFactsStmt,
    ) -> RuntimeResult<ExecHaveObjByExistFactsStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        let exist_family = ExistShapedFact::Exist(PlainExistFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: stmt.param_def.clone(),
            facts: stmt.facts.clone(),
            line_file: Some(stmt.line_file.clone()),
        });

        let verified = self.verify_exist_shaped_fact(&exist_family, verify_state)?;
        let verify_exist = match self.unwrap_plain_exist_verify(verified)? {
            Ok(success) => success,
            Err(failed) => {
                return Ok(ExecHaveObjByExistFactsStmtResult::Failed(
                    ExecHaveObjByExistFactsStmtFailed::Exist(failed),
                ));
            }
        };

        let mut store_and_infer_result = self.define_typed_parameters_in_current_env(
            &stmt.param_def,
            Some(SharedHaveDefinition::HaveObjByExistFacts(Rc::new(
                stmt.clone(),
            ))),
        )?;

        for body_fact in &stmt.facts {
            let as_fact = quantifier_free_fact_to_fact(body_fact.clone());
            let stored = self.store_fact_and_infer(&as_fact)?;
            store_and_infer_result
                .stored_fact_ids
                .extend(stored.stored_fact_ids());
        }

        Ok(ExecHaveObjByExistFactsStmtResult::Success(
            ExecHaveObjByExistFactsStmtSuccessResult {
                statement: stmt.clone(),
                verify_exist,
                store_and_infer_result,
            },
        ))
    }

    fn unwrap_plain_exist_verify(
        &self,
        result: VerifyFactResult,
    ) -> RuntimeResult<Result<VerifyPlainExistFactSuccess, VerifyExistShapedFactFailed>> {
        match result {
            VerifyFactResult::ExistShapedFact(boxed) => match *boxed {
                VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(s)) => {
                    Ok(Ok(s))
                }
                VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Failed(f)) => {
                    Ok(Err(f))
                }
                _ => Err(RuntimeError::InternalBug(
                    "have ...: expected plain exist verify result, got unexpected exist family branch"
                        .to_string(),
                )),
            },
            _ => Err(RuntimeError::InternalBug(
                "have ...: expected ExistFact verify result".to_string(),
            )),
        }
    }
}
