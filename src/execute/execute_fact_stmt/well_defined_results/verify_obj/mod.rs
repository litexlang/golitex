//! Object well-definedness: Success(ByKnown { obj, .. } | ByDef { obj, .. }) | Failed { obj, reason }.
//!
//! Entry matches every Obj variant; families live in sibling modules.
//! ByDef success proofs mirror Obj. Scalar (P0) fills requirement facts.

mod binder;
mod closed_numeric_eval_wd;
mod core;
mod definition_owned_type;
mod entry;
pub(crate) mod fail_to_verify_obj_well_defined;
mod fn_obj_domain_check_result;
mod fn_obj_domain_success;
mod helper;
mod iterated;
mod matrix;
mod obj_well_defined_by_def_common;
mod obj_well_defined_proof;
mod obj_well_defined_proof_by_def;
mod obj_well_defined_proof_ref;
mod preimage;
mod requirement;
mod scalar;
mod sets;
mod structs;
mod unordered_fold_laws;
mod wrap_obj_well_defined_by_def;

pub use entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
pub use fail_to_verify_obj_well_defined::{
    fail_to_verify_obj_well_defined_others, FailToVerifyBoundOperatorObjWellDefinedResult,
    FailToVerifyFnSetObjWellDefined, FailToVerifyFunctionLimitObjWellDefined,
    FailToVerifyFunctionSpaceObjWellDefinedResult, FailToVerifyInfimumObjWellDefined,
    FailToVerifyLimitOperatorObjWellDefinedResult, FailToVerifyObjWellDefinedResult,
    FailToVerifySequenceLiminfObjWellDefined, FailToVerifySequenceLimitObjWellDefined,
    FailToVerifySequenceLimsupObjWellDefined, FailToVerifySupremumObjWellDefined,
};
pub use obj_well_defined_proof::{
    CheckedApplicationDomain, CompactObjWellDefinedProof, DetailedObjWellDefinedProof,
    NormalObjWellDefinedProof, ObjWellDefinedComputation,
};
pub use obj_well_defined_proof_by_def::*;
pub(crate) use obj_well_defined_proof_ref::ObjWellDefinedProofRef;

pub use fn_obj_domain_check_result::{
    FnObjArgumentScope, FnObjDomainCheckResult, FormedFunctionArgument,
};
pub use fn_obj_domain_success::{
    CompactFnObjDomainSuccess, DetailedFnObjDomainSuccess, FnObjDomainSuccess,
    NormalFnObjDomainSuccess,
};

pub(crate) use obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
pub use obj_well_defined_by_def_common::{
    CompactObjWellDefinedByDefCommonStages, DetailedObjWellDefinedByDefCommonStages,
    NormalObjWellDefinedByDefCommonStages,
};
