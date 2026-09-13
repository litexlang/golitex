//! Fact-statement execution: verify, then store and infer.

mod cache_search_proof;
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
mod verify_obj_well_defined;
mod verify_or_fact;
mod verify_state;
pub mod verify_well_defined;

pub use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
pub use result::{ExecFactStmtResult, StoreFactAndInferResult};
pub use verify_atomic_fact::verify_equality::equal_fact_from_let;
pub use verify_atomic_fact::verify_non_equational_atomic_fact::
    NonEquationalAtomicFactSearchProofByBuiltinRule;
pub use verify_fact_result::VerifyFactResult;
pub use verify_state::VerifyState;
pub use verify_well_defined::{
    AtomicFactWellDefinedProof, FactWellDefinedProof, ObjWellDefinedProofByDef,
    ParamTypeWellDefinedProof, VerifyObjResult,
};
