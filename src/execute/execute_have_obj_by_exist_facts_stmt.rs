//! `have x S: facts` — prove synthesized exist, then introduce witnesses.
//!
//! Example:
//!   have left_greater R:
//!       left_greater > 100

use crate::ast::fact::{ExistShapedFact, PlainExistFact};
use crate::ast::stmt::HaveObjByExistFactsStmt;
use crate::execute::execute_fact_stmt::{
    VerifyExistShapedFactFailed, VerifyExistShapedFactResult, VerifyFactResult,
    VerifyPlainExistFactResult, VerifyPlainExistFactSuccess, VerifyState,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::execute::introduce_typed_parameters::SharedHaveDefinition;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::rc::Rc;

pub enum ExecHaveObjByExistFactsStmtFailed {
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
    Exist(VerifyExistShapedFactFailed),
    Context(Box<ExecHaveObjByExistFactsFailure>),
}

pub struct ExecHaveObjByExistFactsFailure {
    pub statement: HaveObjByExistFactsStmt,
    pub exist_family: ExistShapedFact,
    pub failed: VerifyExistShapedFactFailed,
}

// Pipeline: synthesize exist → verify exist → define params + store body facts.
pub struct ExecHaveObjByExistFactsStmtSuccessResult {
    pub statement: HaveObjByExistFactsStmt,
    pub verify_exist: VerifyPlainExistFactSuccess,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
    pub auto_opened_struct_layers: Option<Vec<crate::execute::ReleaseOneStructLayerProof>>,
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
        let verify_state = VerifyState::top_level();

        let exist_family = ExistShapedFact::Exist(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: stmt.param_def.clone(),
            facts: stmt.facts.clone(),
            line_file: Some(stmt.line_file.clone()),
        });

        let verified = self.verify_exist_shaped_fact(&exist_family, verify_state)?;
        let verify_exist = match self.unwrap_plain_exist_verify(verified)? {
            Ok(success) => success,
            Err(failed) => {
                return Ok(ExecHaveObjByExistFactsStmtResult::Failed(
                    ExecHaveObjByExistFactsStmtFailed::Context(Box::new(
                        ExecHaveObjByExistFactsFailure {
                            statement: stmt.clone(),
                            exist_family,
                            failed,
                        },
                    )),
                ));
            }
        };

        let mut store_and_infer_result = self.define_typed_parameters_in_current_env(
            &stmt.param_def,
            Some(SharedHaveDefinition::HaveObjByExistFacts(Rc::new(
                stmt.clone(),
            ))),
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;

        let substitution = super::helper::published_parameter_substitution(self, &stmt.param_def);
        for body_fact in &stmt.facts {
            let body_fact = if substitution.is_empty() {
                body_fact.clone()
            } else {
                self.inst_quantifier_free_fact(body_fact, &substitution)
                    .map_err(|e| RuntimeError::InternalBug(format!("have body publication: {e}")))?
            };
            let as_fact = quantifier_free_fact_to_fact(body_fact);
            let stored = self.store_fact_and_infer(
                &as_fact,
                crate::execute::execute_fact_stmt::VerifyState::top_level(),
            )?;
            store_and_infer_result.push(stored);
        }

        let published = super::helper::published_parameter_list(self, &stmt.param_def)?;
        let auto_opened_struct_layers =
            match self.auto_open_struct_layers_for_typed_parameters(&published, verify_state)? {
                Ok(opened) => opened,
                Err((_, failed)) => {
                    return Ok(ExecHaveObjByExistFactsStmtResult::Failed(
                        ExecHaveObjByExistFactsStmtFailed::AutoOpenStructLayer(failed),
                    ))
                }
            };

        Ok(ExecHaveObjByExistFactsStmtResult::Success(
            ExecHaveObjByExistFactsStmtSuccessResult {
                statement: stmt.clone(),
                verify_exist,
                store_and_infer_result,
                auto_opened_struct_layers,
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
