//! Fact-statement execution: verify, then store and infer.

mod exec_fact_stmt;
mod result;
mod verify;
mod verify_and_fact;
mod verify_atomic_fact;
mod verify_chain_fact;
mod verify_exist_fact;
mod verify_fact_result;
mod verify_forall_fact;
mod verify_forall_fact_with_iff;
mod verify_not_forall_fact;
mod verify_or_fact;
mod verify_state;
pub mod well_defined_results;

pub use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
pub use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
pub use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;
pub use result::{ExecFactStmtResult, ExecFactStmtSuccessResult};
pub use verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRule;
pub use verify_exist_fact::{
    VerifyExistFactFailed, VerifyExistFactResult, VerifyExistUniqueFactResult,
    VerifyPlainExistFactResult, VerifyPlainExistFactSuccess,
};
pub use verify_fact_result::VerifyFactResult;
pub use verify_forall_fact::{
    AssumeDomFactResult, ProveAndStoreThenFactResult, VerifyForallFactResult,
};
pub use verify_or_fact::{
    OrBuiltinRealLineTrichotomyEqLessGreater, OrBuiltinRealLineTrichotomyGreaterEqLess,
    OrBuiltinRealLineTrichotomyLessEqGreater, OrFactSearchProofByBuiltinRule,
    OrFactSearchedProof, VerifyOrFactFailed, VerifyOrFactResult, VerifyOrFactSuccess,
};
pub use verify_state::VerifyState;
pub use well_defined_results::{
    fail_to_verify_obj_well_defined_others, AtomicFactWellDefinedProof, EqualFactWellDefinedProof,
    ExistFactWellDefinedProof, FactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    FailToVerifyEqualFactWellDefinedResult, FailToVerifyExistFactWellDefinedResult,
    FailToVerifyFactWellDefinedResult, FailToVerifyForallFactWellDefinedResult,
    FailToVerifyObjWellDefinedResult, FailToVerifyOrFactWellDefinedResult, ObjWellDefinedProof,
    ObjWellDefinedProofByDef, OrFactWellDefinedProof, VerifyAtomicFactWellDefinedResult,
    VerifyEqualFactWellDefinedResult, VerifyExistFactWellDefinedResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyOrFactWellDefinedResult,
};
