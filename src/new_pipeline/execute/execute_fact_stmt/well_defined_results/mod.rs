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
    AtomicFactWellDefinedProof, EqualFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    FailToVerifyEqualFactWellDefinedResult, VerifyAtomicFactWellDefinedResult,
    VerifyEqualFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_chain_fact::{
    ChainFactWellDefinedProof, FailToVerifyChainFactWellDefinedResult,
    VerifyChainFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_shaped_fact::{
    ExistShapedFactWellDefinedProof, FailToVerifyExistShapedFactWellDefinedResult,
    VerifyExistShapedFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::{
    FailToVerifyForallFactWellDefinedResult, ForallFactWellDefinedProof,
    VerifyForallFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact_with_iff::{
    FailToVerifyForallFactWithIffWellDefinedResult, ForallFactWithIffWellDefinedProof,
    VerifyForallFactWithIffWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_not_forall_fact::{
    FailToVerifyNotForallFactWellDefinedResult, NotForallFactWellDefinedProof,
    VerifyNotForallFactWellDefinedResult,
};
pub use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof, VerifyOrFactWellDefinedResult,
};
pub use well_defined_result::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult,
};
pub use verify_obj::{
    fail_to_verify_obj_well_defined_others, FailToVerifyFnSetObjWellDefined,
    FailToVerifyFunctionSpaceObjWellDefinedResult, FailToVerifyObjWellDefinedResult,
    ObjWellDefinedProof, ObjWellDefinedProofByDef, VerifyObjWellDefinedResult,
};
