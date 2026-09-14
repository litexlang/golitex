//! `trust` statement: verify well-definedness, then store without truth search.
//!
//! Pipeline stages (field order matches):
//! 1. well-definedness of every fact
//! 2. store + infer every fact
//!
//! Atomicity: all WD proofs collected before any store; mid-block WD failure
//! commits nothing.

use crate::new_pipeline::ast::stmt::TrustStmt;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, StoreFactAndInferResult, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

/// `trust` / `trust:` pipeline result.
///
/// Vectors are parallel to `statement.facts`.
pub struct ExecTrustStmtResult {
    pub statement: TrustStmt,
    pub facts_well_defined: Vec<FactWellDefinedProof>,
    pub store_and_infer_results: Vec<StoreFactAndInferResult>,
}

impl Runtime {
    // Mathematical contract: `trust` requires well-definedness of every fact
    // (and its objects) but skips truth verification. Example:
    //   trust 1 + 1 = 3   // ok: WD passes; equality is assumed
    //   trust 1 / 0 = 0   // error: division WD fails
    pub fn exec_trust_stmt(&mut self, stmt: &TrustStmt) -> RuntimeResult<ExecTrustStmtResult> {
        let verify_state = trust_verify_state();

        let mut facts_well_defined = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            facts_well_defined.push(self.verify_fact_well_definedness(fact, verify_state.clone())?);
        }

        let mut store_and_infer_results = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            store_and_infer_results.push(self.store_fact_and_infer(fact)?);
        }

        Ok(ExecTrustStmtResult {
            statement: stmt.clone(),
            facts_well_defined,
            store_and_infer_results,
        })
    }
}

pub(super) fn trust_verify_state() -> VerifyState {
    VerifyState {
        can_use_forall_fact: true,
        can_use_known_algebraic_rewrite: true,
        store_well_defined_fact: true,
    }
}
