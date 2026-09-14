//! Object well-definedness: ByCache | ByDef.
//!
//! Entry matches every Obj variant; families live in sibling modules.
//! Scalar (P0) also verifies requirement facts into requirement_fact_verified.

mod core;
mod entry;
mod helper;
mod iterated;
mod requirement;
mod scalar;
mod sets;
mod structs;

pub use entry::{ObjWellDefinedProofByDef, VerifyObjResult};
