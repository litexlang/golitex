//! Fact-statement execution: verify the goal, then store and infer.
//! Verify closes the current goal; store+infer writes accepted facts and runs
//! local inference — not a second open-ended proof search.

mod exec_fact_stmt;
mod result;
mod strategy_search;
mod verify;
pub mod verify_and_fact;
pub mod verify_atomic_fact;
pub mod verify_chain_fact;
pub mod verify_exist_shaped_fact;
mod verify_fact_result;
pub mod verify_forall_fact;
pub mod verify_forall_fact_with_iff;
mod verify_in_strategy;
pub mod verify_not_forall_fact;
pub mod verify_or_fact;
mod verify_state;
pub mod well_defined_results;

pub use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
pub use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
pub use crate::store_fact_and_infer::StoreFactAndInferResult;
pub use result::{ExecFactStmtResult, ExecFactStmtSuccessResult};
pub use verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRule;
pub use verify_exist_shaped_fact::{
    VerifyExistShapedFactFailed, VerifyExistShapedFactResult, VerifyExistUniqueFactResult,
    VerifyExistUniqueFactSuccess, VerifyPlainExistFactResult, VerifyPlainExistFactSuccess,
};
pub use verify_fact_result::VerifyFactResult;
pub use verify_forall_fact::{
    AssumeDomFactResult, ProveAndStoreThenFactResult, VerifyForallFactFailed,
    VerifyForallFactResult,
};
pub use verify_or_fact::{
    OrBuiltinRealLineTrichotomyEqLessGreater, OrBuiltinRealLineTrichotomyGreaterEqLess,
    OrBuiltinRealLineTrichotomyLessEqGreater, OrFactSearchProofByBuiltinRule,
    OrFactSearchedProof, VerifyOrFactFailed, VerifyOrFactResult, VerifyOrFactSuccess,
};
pub use strategy_search::StrategySearch;
pub use verify_state::VerifyState;
pub use well_defined_results::{
    fail_to_verify_obj_well_defined_others, AtomicFactWellDefinedProof, EqualFactWellDefinedProof,
    ExistShapedFactWellDefinedProof, FactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
    FailToVerifyEqualFactWellDefinedResult, FailToVerifyExistShapedFactWellDefinedResult,
    FailToVerifyFactWellDefinedResult, FailToVerifyForallFactWellDefinedResult,
    FailToVerifyObjWellDefinedResult, FailToVerifyOrFactWellDefinedResult, ObjWellDefinedProof,
    ObjWellDefinedProofByDef, OrFactWellDefinedProof, VerifyAtomicFactWellDefinedResult,
    VerifyEqualFactWellDefinedResult, VerifyExistShapedFactWellDefinedResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyOrFactWellDefinedResult,
};
pub use verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::alpha_equal_helper::fn_sets_alpha_equal;
