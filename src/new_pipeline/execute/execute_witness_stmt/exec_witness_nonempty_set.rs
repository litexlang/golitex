//! `witness $is_nonempty_set(S) from o` — prove nonemptiness by a concrete member.
//!
//! Mathematical contract:
//! - WD(o), WD(S);
//! - verify `o $in S`;
//! - store `IsNonemptySetFact(S)`.
//! No FnSet/codomain shortcut (legacy weirdness deliberately omitted).
//!
//! Example:
//!   1 $in {1, 2}
//!   witness $is_nonempty_set({1, 2}) from 1

use crate::new_pipeline::ast::fact::{AtomicFact, Fact, InFact, IsNonemptySetFact};
use crate::new_pipeline::ast::stmt::WitnessNonemptySet;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

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
    Membership(VerifyFactResult),
}

pub struct ExecWitnessNonemptySetStmtSuccessResult {
    pub statement: WitnessNonemptySet,
    pub obj_well_defined: VerifyObjWellDefinedResult,
    pub set_well_defined: VerifyObjWellDefinedResult,
    pub membership_check: VerifyFactResult,
    pub store_and_infer_result: StoreFactAndInferResult,
}

impl Runtime {
    // Pipeline: WD(o) → WD(S) → verify `o $in S` → store `$is_nonempty_set(S)`.
    pub(in crate::new_pipeline::execute) fn exec_witness_nonempty_set(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> RuntimeResult<ExecWitnessNonemptySetStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
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
            fact_id: self.ids.allocate_fact_id(),
            element: stmt.obj.clone(),
            set: stmt.set.clone(),
            line_file: Some(stmt.line_file.clone()),
        }));
        let membership_check = self.verify_fact(&membership_fact, verify_state)?;
        if membership_check.is_failed() {
            return Ok(ExecWitnessNonemptySetStmtResult::Failed(
                ExecWitnessNonemptySetStmtFailed::Membership(membership_check),
            ));
        }

        let nonempty_fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id: self.ids.allocate_fact_id(),
            set: stmt.set.clone(),
            line_file: Some(stmt.line_file.clone()),
        }));
        let store_and_infer_result = self.store_fact_and_infer(&nonempty_fact)?;

        Ok(ExecWitnessNonemptySetStmtResult::Success(
            ExecWitnessNonemptySetStmtSuccessResult {
                statement: stmt.clone(),
                obj_well_defined,
                set_well_defined,
                membership_check,
                store_and_infer_result,
            },
        ))
    }
}
