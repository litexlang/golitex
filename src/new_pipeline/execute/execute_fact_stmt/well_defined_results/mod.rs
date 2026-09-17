//! Well-definedness verification for new_pipeline.
//!
//! Object WD and the thin Fact WD dispatcher live here. Per-fact WD types and
//! algorithms live under each verify_*_fact module; this mod re-exports them.
//! Prefer `verify_xxx_fact_well_definedness` when the Fact shape is known.

mod verify_fact;
mod verify_obj;
mod verify_param_type;
mod well_defined_result;

pub use crate::new_pipeline::execute::execute_fact_stmt::verify_and_fact::{
    AndFactWellDefinedProof, FailToVerifyAndFactWellDefinedResult, VerifyAndFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    VerifyAtomicFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_chain_fact::{
    ChainFactWellDefinedProof, FailToVerifyChainFactWellDefinedResult,
    VerifyChainFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::{
    ExistFactWellDefinedProof, FailToVerifyExistFactWellDefinedResult,
    VerifyExistFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult;
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult;
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult;
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof, VerifyOrFactWellDefinedResult,
};
pub use well_defined_result::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult,
};
pub use verify_obj::{
    FailToVerifyObjWellDefinedResult, ObjWellDefinedProofByDef, VerifyObjWellDefinedResult,
};
