//! Point and set preimage WD retain their complete-domain and bounded-builder proofs.
use crate::ast::obj::{Obj, Preimage, PreimageSet};
use crate::execute::execute_fact_stmt::{VerifyState, RuntimeResult};
use crate::runtime::Runtime;
use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use super::obj_well_defined_proof_by_def::{ObjWellDefinedProofByDef, FunctionSpaceObjWellDefinedProofByDef, PreimageObjWellDefinedProof, PreimageSetObjWellDefinedProof};
use super::fail_to_verify_obj_well_defined::{FailToVerifyObjWellDefinedResult, FailToVerifyFunctionSpaceObjWellDefinedResult, FailToVerifyPreimageObjWellDefined, FailToVerifyPreimageSetObjWellDefined};

impl Runtime {
    pub(super) fn verify_preimage_obj_well_definedness(
        &mut self, value: &Preimage, state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let root: Obj = value.clone().into();
        let stages = self.verify_binary_obj_well_definedness_by_def(&value.function, &value.value, state)?;
        if !stages.is_fully_known() {
            return Ok(VerifyObjWellDefinedResult::Failed { obj: root.clone(), reason:
                FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::Preimage(
                    FailToVerifyPreimageObjWellDefined::Domain(stages.into_common_fail(&root)))) });
        }
        let construction = match self.verify_function_preimage_construction(&root, state)? {
            Ok(proof) => proof,
            Err(failed) => return Ok(VerifyObjWellDefinedResult::Failed { obj: root, reason:
                FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::Preimage(
                    FailToVerifyPreimageObjWellDefined::Construction(failed))) }),
        };
        let (child_obj_well_defined, requirement_fact_verified) = stages.into_success_child_proofs();
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef { obj: root, proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::Preimage(
                PreimageObjWellDefinedProof { child_obj_well_defined, requirement_fact_verified, construction })) }))
    }

    pub(super) fn verify_preimage_set_obj_well_definedness(
        &mut self, value: &PreimageSet, state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let root: Obj = value.clone().into();
        let mut stages = self.verify_binary_obj_well_definedness_by_def(&value.function, &value.target_set, state)?;
        if stages.is_fully_known() {
            stages.requirement_fact_verified.push(self.require_is_set(&value.target_set, state,
                "preimage_set: target must be a set".to_string())?);
        }
        if !stages.is_fully_known() {
            return Ok(VerifyObjWellDefinedResult::Failed { obj: root.clone(), reason:
                FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::PreimageSet(
                    FailToVerifyPreimageSetObjWellDefined::Domain(stages.into_common_fail(&root)))) });
        }
        let construction = match self.verify_function_preimage_construction(&root, state)? {
            Ok(proof) => proof,
            Err(failed) => return Ok(VerifyObjWellDefinedResult::Failed { obj: root, reason:
                FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::PreimageSet(
                    FailToVerifyPreimageSetObjWellDefined::Construction(failed))) }),
        };
        let (child_obj_well_defined, requirement_fact_verified) = stages.into_success_child_proofs();
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef { obj: root, proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::PreimageSet(
                PreimageSetObjWellDefinedProof { child_obj_well_defined, requirement_fact_verified, construction })) }))
    }
}
