//! `release struct def e` — verify membership, then open one struct layer.
//!
//! Aligns with legacy `exec_release_struct_def_stmt`:
//! 1. resolve definition-owned `&Struct` carrier for `e`
//! 2. prove `e $in &Struct` (soft-fail if unknown)
//! 3. `release_one_struct_layer` (bridges + field carriers + `<=>:` laws)
//!
//! Typical use: nested struct field. Direct `&Outer` bind auto-opens only the
//! outer layer; an inner `&Inner` field still needs an explicit release.
//!
//! Example:
//!   struct Coordinates:
//!       x R
//!       y R
//!       <=>:
//!           x = 0
//!   struct TaggedPoint:
//!       point &Coordinates
//!       tag N
//!   trust have p &TaggedPoint
//!   release struct def p.point
//!   p.point.x = 0

use crate::new_pipeline::ast::fact::{AtomicFact, Fact, InFact};
use crate::new_pipeline::ast::obj::{Obj, StructAndFieldAccessObj, StructObj};
use crate::new_pipeline::ast::stmt::ReleaseStructDefStmt;
use crate::new_pipeline::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::new_pipeline::execute::release_one_struct_layer::{
    FailToReleaseOneStructLayer, ReleaseOneStructLayerProof, ReleaseOneStructLayerResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum ExecReleaseStructDefStmtFailed {
    NoDefinitionOwnedCarrier { obj: Obj },
    Membership(VerifyFactResult),
    Release(FailToReleaseOneStructLayer),
}

pub struct ExecReleaseStructDefStmtSuccess {
    pub statement: ReleaseStructDefStmt,
    pub struct_obj: StructObj,
    pub membership: VerifyFactResult,
    pub release: ReleaseOneStructLayerProof,
}

pub enum ExecReleaseStructDefStmtResult {
    Success(ExecReleaseStructDefStmtSuccess),
    Failed(ExecReleaseStructDefStmtFailed),
}

impl ExecReleaseStructDefStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Soft miss: Ok(Failed); operational bug: Err(...).
    // Runs inside exec_stmt's temp env so Failed discards any partial stores.
    pub(in crate::new_pipeline::execute) fn exec_release_struct_def_stmt(
        &mut self,
        stmt: &ReleaseStructDefStmt,
    ) -> RuntimeResult<ExecReleaseStructDefStmtResult> {
        let Some(struct_obj) = self.resolve_definition_struct_carrier(&stmt.obj) else {
            return Ok(ExecReleaseStructDefStmtResult::Failed(
                ExecReleaseStructDefStmtFailed::NoDefinitionOwnedCarrier {
                    obj: stmt.obj.clone(),
                },
            ));
        };

        let membership_fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.ids.allocate_fact_id(),
            element: stmt.obj.clone(),
            set: Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(struct_obj.clone())),
            line_file: Some(stmt.line_file.clone()),
        }));
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };
        let membership = self.verify_fact(&membership_fact, verify_state)?;
        if membership.is_failed() {
            return Ok(ExecReleaseStructDefStmtResult::Failed(
                ExecReleaseStructDefStmtFailed::Membership(membership),
            ));
        }

        match self.release_one_struct_layer(&stmt.obj, &struct_obj)? {
            ReleaseOneStructLayerResult::Success(release) => Ok(
                ExecReleaseStructDefStmtResult::Success(ExecReleaseStructDefStmtSuccess {
                    statement: stmt.clone(),
                    struct_obj,
                    membership,
                    release,
                }),
            ),
            ReleaseOneStructLayerResult::Failed(failed) => {
                Ok(ExecReleaseStructDefStmtResult::Failed(
                    ExecReleaseStructDefStmtFailed::Release(failed),
                ))
            }
        }
    }
}
