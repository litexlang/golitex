//! Tier 1 frozen backbone: Object WD entry (known-memory lookup + dispatch handoff).
//!
//! Soft miss is `Ok(Failed { .. })` — ill-formed / not WD, not "unknown theorem".
//! Must-prove callers reject that at their boundary.
//! Family routing lives in Tier 2 `dispatch_obj_well_definedness.rs`.

use super::fail_to_verify_obj_well_defined::FailToVerifyObjWellDefinedResult;
pub use super::obj_well_defined_proof::ObjWellDefinedProof;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Top-level object WD: Success(proof) | Failed { obj, reason }. Proof never embeds Fail.
pub enum VerifyObjWellDefinedResult {
    Success(ObjWellDefinedProof),
    Failed {
        obj: Obj,
        reason: FailToVerifyObjWellDefinedResult,
    },
}

impl VerifyObjWellDefinedResult {
    pub fn as_detailed_success(
        &self,
    ) -> RuntimeResult<Option<&super::DetailedObjWellDefinedProof>> {
        match self {
            Self::Success(proof) => proof.as_detailed().map(Some),
            Self::Failed { .. } => Ok(None),
        }
    }

    pub fn as_detailed_success_mut(
        &mut self,
    ) -> RuntimeResult<Option<&mut super::DetailedObjWellDefinedProof>> {
        match self {
            Self::Success(proof) => proof.as_detailed_mut().map(Some),
            Self::Failed { .. } => Ok(None),
        }
    }

    pub fn into_detailed_success(
        self,
    ) -> RuntimeResult<Option<super::DetailedObjWellDefinedProof>> {
        match self {
            Self::Success(proof) => proof.into_detailed().map(Some),
            Self::Failed { .. } => Ok(None),
        }
    }

    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed { .. })
    }

    pub fn obj(&self) -> &Obj {
        match self {
            Self::Success(proof) => proof.obj(),
            Self::Failed { obj, .. } => obj,
        }
    }
}

impl Runtime {
    // Known-memory lookup across the env stack, then prove by definition.
    // This entry returns evidence without registering its own result. Function
    // candidates may register completed children in their retained local scope;
    // checked direct atomic subjects are registered at statement commit.
    pub fn verify_obj_well_definedness(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        if let Some(wd_id) = self.well_defined_visible_in_stack(obj) {
            return Ok(VerifyObjWellDefinedResult::Success(
                ObjWellDefinedProof::by_known(self.result_detail(), obj, wd_id),
            ));
        }

        // Eval closed-numeric mode: children + domain checks only (no per-node
        // `$in C`). See closed_numeric_eval_wd.rs.
        if self.eval_closed_numeric_source_wd
            && crate::rational_expression::ClosedNumericExpr::try_from_obj(obj).is_some()
        {
            return self.verify_closed_numeric_source_node_without_carrier(obj, verify_state);
        }

        self.dispatch_obj_well_definedness(obj, verify_state)
    }
}
