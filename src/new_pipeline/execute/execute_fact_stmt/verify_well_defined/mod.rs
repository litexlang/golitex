//! Well-definedness verification for new_pipeline.
//!
//! Main entries classify by AST shape, then dispatch.
//! Object WD top-level result is ByKnown | ByDef | FailToVerifyWellDefined.
//! Atomic/fact WD: *Proof is success-only; Verify*WellDefinedResult = Success|Failed.

mod verify_atomic_fact;
mod verify_fact;
mod verify_obj;
mod verify_param_type;

pub use verify_atomic_fact::{AtomicFactWellDefinedProof, VerifyAtomicFactWellDefinedResult};
pub use verify_fact::{FactWellDefinedProof, VerifyFactWellDefinedResult};
pub use verify_obj::{
    FailToVerifyObjWellDefinedResult, ObjWellDefinedProofByDef, VerifyObjWellDefinedResult,
};
