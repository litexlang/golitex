//! `witness $is_nonempty_set(S) from o [:]` — prove nonemptiness by a concrete member.
//!
//! Mathematical contract:
//! - WD(o), WD(S);
//! - optional local proof body (full Stmt);
//! - verify `o $in S` in that local env;
//! - store `IsNonemptySetFact(S)`.
//! No FnSet/codomain shortcut (legacy weirdness deliberately omitted).
//!
//! Example:
//!   1 $in {1, 2}
//!   witness $is_nonempty_set({1, 2}) from 1

use crate::ast::fact::{AtomicFact, Fact, InFact, IsNonemptySetFact};
use crate::ast::stmt::WitnessNonemptySet;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_proof_block_stmt::{run_proof_body_stmts, ProofBlockBodyFailed};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub enum ExecWitnessNonemptySetStmtResult {
    Success(ExecWitnessNonemptySetStmtSuccessResult),
    Failed(ExecWitnessNonemptySetStmtFailed),
}

impl ExecWitnessNonemptySetStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecWitnessNonemptySetStmtFailed {
    ObjWd(VerifyObjWellDefinedResult),
    SetWd(VerifyObjWellDefinedResult),
    ProofBody(ProofBlockBodyFailed),
    Membership(VerifyFactResult),
}

// Stage order: obj WD → set WD → proof_steps → membership → local_env → store.
pub struct ExecWitnessNonemptySetStmtSuccessResult {
    pub statement: WitnessNonemptySet,
    pub obj_well_defined: VerifyObjWellDefinedResult,
    pub set_well_defined: VerifyObjWellDefinedResult,
    pub proof_steps: Vec<ExecStmtResult>,
    pub membership_check: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub store_and_infer_result: StoreFactAndInferResult,
}

impl Runtime {
    // Pipeline: WD(o) → WD(S) → local(proof → `o $in S`) → store `$is_nonempty_set(S)`.
    pub(in crate::execute) fn exec_witness_nonempty_set(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> RuntimeResult<ExecWitnessNonemptySetStmtResult> {
        let verify_state = VerifyState {
            can_use_builtin_rule: true,
            remaining_deep_search_depth: VerifyState::TOP_DEEP_SEARCH_DEPTH,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
            equality_class_search: crate::execute::execute_fact_stmt::EqualityClassSearchMode::AllowPeerComparison,
        };

        let obj_well_defined =
            self.verify_obj_well_definedness(&stmt.obj, verify_state.clone())?;
        if obj_well_defined.is_failed() {
            return Ok(ExecWitnessNonemptySetStmtResult::Failed(
                ExecWitnessNonemptySetStmtFailed::ObjWd(obj_well_defined),
            ));
        }

        let set_well_defined =
            self.verify_obj_well_definedness(&stmt.set, verify_state.clone())?;
        if set_well_defined.is_failed() {
            return Ok(ExecWitnessNonemptySetStmtResult::Failed(
                ExecWitnessNonemptySetStmtFailed::SetWd(set_well_defined),
            ));
        }

        let membership_fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: stmt.obj.clone(),
            set: stmt.set.clone(),
            line_file: Some(stmt.line_file.clone()),
        }));

        let (local_outcome, local_env) = self.run_in_local_env_and_take_env(|rt| {
            let proof_steps = match run_proof_body_stmts(rt, &stmt.proof)? {
                Ok(steps) => steps,
                Err(failed) => {
                    return Ok(Err(ExecWitnessNonemptySetStmtFailed::ProofBody(failed)));
                }
            };
            let membership_check = rt.verify_fact(&membership_fact, verify_state.clone())?;
            if membership_check.is_failed() {
                return Ok(Err(ExecWitnessNonemptySetStmtFailed::Membership(
                    membership_check,
                )));
            }
            Ok(Ok((proof_steps, membership_check)))
        })?;

        let (proof_steps, membership_check) = match local_outcome {
            Ok(v) => v,
            Err(failed) => {
                return Ok(ExecWitnessNonemptySetStmtResult::Failed(failed));
            }
        };

        let nonempty_fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: stmt.set.clone(),
            line_file: Some(stmt.line_file.clone()),
        }));
        let store_and_infer_result = self.store_fact_and_infer(&nonempty_fact)?;

        Ok(ExecWitnessNonemptySetStmtResult::Success(
            ExecWitnessNonemptySetStmtSuccessResult {
                statement: stmt.clone(),
                obj_well_defined,
                set_well_defined,
                proof_steps,
                membership_check,
                local_env,
                store_and_infer_result,
            },
        ))
    }
}
