//! `trust have` statement: WD param types and body facts, then bind and store.
//!
//! Pipeline stages (field order matches):
//! 1. param-type WD
//! 2. body-fact WD
//! 3. define params (bindings + type-fact placeholders)
//! 4. store + infer body facts
//!
//! Skips nonempty/truth obligations that ordinary `have` would prove.
//! Atomicity: all WD collected before any env mutation.

use super::super::exec_stmt_result::StoreHaveObjAndInferResult;
use super::exec_trust_stmt::trust_verify_state;
use crate::new_pipeline::ast::stmt::TrustHaveStmt;
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, ParamTypeWellDefinedProof, StoreFactAndInferResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

/// `trust have` pipeline result.
///
/// `body_facts_well_defined` and `body_store_and_infer_results` are parallel
/// to `statement.facts`.
pub struct ExecTrustHaveStmtResult {
    pub statement: TrustHaveStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub body_facts_well_defined: Vec<FactWellDefinedProof>,
    pub defined_param_store_and_infer: StoreHaveObjAndInferResult,
    pub body_store_and_infer_results: Vec<StoreFactAndInferResult>,
}

impl Runtime {
    // Mathematical contract: `trust have` checks WD of parameter carriers and
    // body facts, skips nonempty and truth proofs, then assumes the bindings
    // and body facts. Example:
    //   trust have a R:
    //       a = 0
    //   // R is WD; a is bound; a = 0 is assumed after its WD succeeds
    pub fn exec_trust_have_stmt(
        &mut self,
        stmt: &TrustHaveStmt,
    ) -> RuntimeResult<ExecTrustHaveStmtResult> {
        let verify_state = trust_verify_state();

        let param_type_well_defined =
            self.verify_typed_parameters_well_definedness(&stmt.param_def, verify_state.clone())?;
        for proof in &param_type_well_defined {
            if proof.is_unknown() {
                return Err(RuntimeError::Unknown(
                    "trust have: unable to establish well-definedness of parameter type"
                        .to_string(),
                ));
            }
        }

        let mut body_facts_well_defined = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            let wd = self.verify_fact_well_definedness(fact, verify_state.clone())?;
            if wd.is_unknown() {
                return Err(RuntimeError::Unknown(
                    "trust have: unable to establish well-definedness of body fact".to_string(),
                ));
            }
            body_facts_well_defined.push(wd);
        }

        let defined_param_store_and_infer = self.define_trust_have_params(stmt)?;

        let mut body_store_and_infer_results = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            body_store_and_infer_results.push(self.store_fact_and_infer(fact)?);
        }

        Ok(ExecTrustHaveStmtResult {
            statement: stmt.clone(),
            param_type_well_defined,
            body_facts_well_defined,
            defined_param_store_and_infer,
            body_store_and_infer_results,
        })
    }

    fn define_trust_have_params(
        &mut self,
        stmt: &TrustHaveStmt,
    ) -> RuntimeResult<StoreHaveObjAndInferResult> {
        let mut stored_fact_ids = Vec::new();
        for group in &stmt.param_def.groups {
            for identifier in &group.params {
                if self
                    .top_exec_env()
                    .definitions
                    .identifiers
                    .contains_key(&identifier.name)
                {
                    return Err(RuntimeError::Invariant(format!(
                        "identifier `{}` is already defined in this ExecEnv",
                        identifier.name
                    )));
                }
                self.top_exec_env_mut().definitions.identifiers.insert(
                    identifier.name.clone(),
                    DefinedIdentifierInfo {
                        identifier: identifier.clone(),
                    },
                );
                // Type facts belong in KnownFactMemory once that store is wired.
                stored_fact_ids.push(self.ids.allocate_fact_id());
            }
        }
        Ok(StoreHaveObjAndInferResult { stored_fact_ids })
    }
}
