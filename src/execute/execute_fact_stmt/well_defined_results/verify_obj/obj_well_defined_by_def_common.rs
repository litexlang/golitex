use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::VerifyObjWellDefinedResult;

use super::entry::ObjWellDefinedProof;
use super::fail_to_verify_obj_well_defined::FailToVerifyObjWellDefinedByDefCommon;

// Shared building bag for by-def WD before packing into an Obj-mirrored proof.
// Success proofs must not keep soft-fails; use finish_by_def after building.
pub struct ObjWellDefinedByDefCommonStages {
    pub child_obj_well_defined: Vec<VerifyObjWellDefinedResult>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ObjWellDefinedByDefCommonStages {
    pub fn leaf() -> Self {
        Self {
            child_obj_well_defined: Vec::new(),
            requirement_fact_verified: Vec::new(),
        }
    }

    pub fn from_children(child_obj_well_defined: Vec<VerifyObjWellDefinedResult>) -> Self {
        Self {
            child_obj_well_defined,
            requirement_fact_verified: Vec::new(),
        }
    }

    pub fn with_requirements(mut self, requirement_fact_verified: Vec<VerifyFactResult>) -> Self {
        self.requirement_fact_verified = requirement_fact_verified;
        self
    }

    pub fn is_fully_known(&self) -> bool {
        for child in &self.child_obj_well_defined {
            if child.is_failed() {
                return false;
            }
        }
        for req in &self.requirement_fact_verified {
            if req.is_failed() {
                return false;
            }
        }
        true
    }

    pub fn into_common_fail(self, root: &Obj) -> FailToVerifyObjWellDefinedByDefCommon {
        for child_result in self.child_obj_well_defined {
            if let VerifyObjWellDefinedResult::Failed { obj, reason } = child_result {
                return FailToVerifyObjWellDefinedByDefCommon::Child {
                    obj,
                    child: Box::new(reason),
                };
            }
        }
        for req in self.requirement_fact_verified {
            if req.is_failed() {
                return FailToVerifyObjWellDefinedByDefCommon::Requirement {
                    obj: root.clone(),
                    result: req,
                };
            }
        }
        FailToVerifyObjWellDefinedByDefCommon::Others(
            "object well-definedness failed without child or requirement detail".to_string(),
        )
    }

    // Pack only after is_fully_known; drops soft-fail variants.
    pub fn into_success_child_proofs(
        self,
    ) -> (Vec<Box<ObjWellDefinedProof>>, Vec<VerifyFactResult>) {
        let mut children = Vec::with_capacity(self.child_obj_well_defined.len());
        for result in self.child_obj_well_defined {
            match result {
                VerifyObjWellDefinedResult::Success(proof) => children.push(Box::new(proof)),
                VerifyObjWellDefinedResult::Failed { .. } => {
                    unreachable!("into_success_child_proofs only on fully-known stages")
                }
            }
        }
        (children, self.requirement_fact_verified)
    }
}
