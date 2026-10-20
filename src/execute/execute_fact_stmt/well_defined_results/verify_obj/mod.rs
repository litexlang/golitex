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
mod helper;
mod iterated;
mod obj_well_defined_by_def_common;
mod obj_well_defined_proof_by_def;
mod preimage;
mod requirement;
mod scalar;
mod sets;
mod structs;
mod unordered_fold_laws;
mod wrap_obj_well_defined_by_def;

pub use entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
pub use fail_to_verify_obj_well_defined::{
    fail_to_verify_obj_well_defined_others, FailToVerifyFnSetObjWellDefined,
    FailToVerifyFunctionLimitObjWellDefined, FailToVerifyFunctionSpaceObjWellDefinedResult,
    FailToVerifyLimitOperatorObjWellDefinedResult, FailToVerifyObjWellDefinedResult,
    FailToVerifySequenceLimitObjWellDefined,
};
pub use obj_well_defined_proof_by_def::*;
