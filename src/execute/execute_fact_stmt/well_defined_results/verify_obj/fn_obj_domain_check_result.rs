use super::fail_to_verify_obj_well_defined::FailToVerifyFnObjObjWellDefined;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::prelude::*;

/// One candidate's ordered checks and the local scope that owns their WD IDs.
pub struct FnObjDomainCheckResult {
    pub stages: ObjWellDefinedByDefCommonStages,
    pub scope: FnObjArgumentScope,
}

pub struct FnObjArgumentScope {
    pub formed_children: Vec<FormedFunctionArgument>,
    pub local_env: Box<ExecEnv>,
}

pub struct FormedFunctionArgument {
    pub child_index: usize,
    pub wd_id: WellDefinednessId,
}

impl FnObjDomainCheckResult {
    pub fn into_success(
        self,
        detail: crate::result_detail::OutputDetail,
    ) -> RuntimeResult<super::FnObjDomainSuccess> {
        self.stages.require_mode(detail)?;
        use super::{
            CompactFnObjDomainSuccess, DetailedFnObjDomainSuccess, FnObjDomainSuccess,
            NormalFnObjDomainSuccess,
        };
        use crate::result_detail::OutputDetail;
        if !self.stages.is_fully_known() {
            return Err(RuntimeError::InternalBug(
                "failed function argument checks used as success".into(),
            ));
        }
        Ok(match self.stages.detail() {
            OutputDetail::Compact => FnObjDomainSuccess::Compact(CompactFnObjDomainSuccess {}),
            OutputDetail::Normal => FnObjDomainSuccess::Normal(NormalFnObjDomainSuccess {}),
            OutputDetail::Detailed => {
                let (child_obj_well_defined, requirement_fact_verified, argument_scope) =
                    self.into_success_child_proofs();
                FnObjDomainSuccess::Detailed(DetailedFnObjDomainSuccess {
                    child_obj_well_defined,
                    requirement_fact_verified,
                    argument_scope,
                })
            }
        })
    }

    pub fn prepend_child(&mut self, child: VerifyObjWellDefinedResult) -> RuntimeResult<()> {
        self.stages.prepend_child(child)?;
        for formed in &mut self.scope.formed_children {
            formed.child_index += 1;
        }
        Ok(())
    }

    pub fn into_success_child_proofs(
        self,
    ) -> (
        Vec<Box<ObjWellDefinedProof>>,
        Vec<VerifyFactResult>,
        Option<FnObjArgumentScope>,
    ) {
        let (children, requirements) = self.stages.into_success_child_proofs();
        (children, requirements, Some(self.scope))
    }

    pub fn into_failure(self) -> FailToVerifyFnObjObjWellDefined {
        FailToVerifyFnObjObjWellDefined::Candidate(Box::new(self))
    }
}
