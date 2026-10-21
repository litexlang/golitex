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
    pub fn prepend_child(&mut self, child: VerifyObjWellDefinedResult) {
        self.stages.child_obj_well_defined.insert(0, child);
        for formed in &mut self.scope.formed_children {
            formed.child_index += 1;
        }
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
