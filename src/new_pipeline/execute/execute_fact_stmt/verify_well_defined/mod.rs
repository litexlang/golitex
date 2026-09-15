//! Well-definedness verification for new_pipeline.
//!
//! Main entries classify by AST shape, then dispatch.
//! Object WD top-level result is only ByCache | ByDef.

mod verify_atomic_fact;
mod verify_fact;
mod verify_obj;
mod verify_param_type;

pub use verify_atomic_fact::AtomicFactWellDefinedProof;
pub use verify_fact::FactWellDefinedProof;
pub use verify_obj::{
    FailToVerifyWellDefinedResult, ObjWellDefinedProofByDef, VerifyObjWellDefinedResult,
};
pub use verify_param_type::ParamTypeWellDefinedProof;
