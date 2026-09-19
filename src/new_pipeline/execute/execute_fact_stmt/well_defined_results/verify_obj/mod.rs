//! Object well-definedness: Success(ByKnown | ByDef) | Failed.
//!
//! Entry matches every Obj variant; families live in sibling modules.
//! ByDef success proofs mirror Obj. Scalar (P0) fills requirement facts.

mod binder;
mod core;
mod entry;
mod fail_to_verify_obj_well_defined;
mod helper;
mod iterated;
mod obj_well_defined_by_def_common;
mod obj_well_defined_proof_by_def;
mod requirement;
mod scalar;
mod sets;
mod structs;
mod wrap_obj_well_defined_by_def;

pub use entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
pub use fail_to_verify_obj_well_defined::{
    fail_to_verify_obj_well_defined_others, FailToVerifyObjWellDefinedResult,
};
pub use obj_well_defined_proof_by_def::ObjWellDefinedProofByDef;
