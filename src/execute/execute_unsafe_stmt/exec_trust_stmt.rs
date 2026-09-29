//! `trust` statement: verify well-definedness, then store without truth search.
//!
//! Pipeline stages (field order matches):
//! 1. well-definedness of every fact
//! 2. store + infer every fact
//!
//! Atomicity: all WD proofs collected before any store; mid-block WD failure
//! commits nothing.

use crate::ast::stmt::TrustStmt;
use crate::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, StoreFactAndInferResult,
    VerifyFactWellDefinedResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};

/// `trust` / `trust:` success payload.
///
/// Vectors are parallel to `statement.facts`.
pub struct ExecTrustStmtSuccessResult {
    pub statement: TrustStmt,
    pub facts_well_defined: Vec<FactWellDefinedProof>,
    pub store_and_infer_results: Vec<StoreFactAndInferResult>,
}

pub enum ExecTrustStmtResult {
    Success(ExecTrustStmtSuccessResult),
    Failed(FailToVerifyFactWellDefinedResult),
}

impl ExecTrustStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Mathematical contract: `trust` requires well-definedness of every fact
    // (and its objects) but skips truth verification. Example:
    //   trust 1 + 1 = 3   // ok: WD passes; equality is assumed
    //   trust 1 / 0 = 0   // soft fail: division WD fails
    pub(in crate::execute) fn exec_trust_stmt(
        &mut self,
        stmt: &TrustStmt,
    ) -> RuntimeResult<ExecTrustStmtResult> {
        let verify_state = trust_verify_state();

        let mut facts_well_defined = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            match self.verify_fact_well_definedness(fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    facts_well_defined.push(proof);
                }
                VerifyFactWellDefinedResult::Failed(reason) => {
                    return Ok(ExecTrustStmtResult::Failed(reason));
                }
            }
        }

        let mut store_and_infer_results = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            store_and_infer_results.push(self.store_fact_and_infer(fact)?);
        }

        Ok(ExecTrustStmtResult::Success(ExecTrustStmtSuccessResult {
            statement: stmt.clone(),
            facts_well_defined,
            store_and_infer_results,
        }))
    }
}

pub(super) fn trust_verify_state() -> VerifyState {
    VerifyState {
        can_use_builtin_rule: true,
        can_use_def_and_known_forall_and_known_strategy: true,
        can_use_rewrite: true,
        store_well_defined_fact: true,
        builtin_strategy_depth_remaining: VerifyState::BUILTIN_STRATEGY_DEPTH_LIMIT,
    }
}
