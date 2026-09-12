//! Fact-statement execution: verify, then store and infer.

mod cache_search_proof;
mod native_equal;
pub use native_equal::equal_fact_from_let;
mod result;
mod verify;
mod verify_atomic_fact;
mod verify_fact_result;
mod verify_obj_well_defined;
mod verify_state;
pub mod verify_well_defined;

pub use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
pub use result::{ExecFactStmtResult, StoreFactAndInferResult2};
pub use verify_state::VerifyState2;
pub use verify_well_defined::{
    AtomicFactWellDefinedProof, FactWellDefinedProof, ObjWellDefinedProofByDef,
    ParamTypeWellDefinedProof, VerifyObjResult,
};
