//! Fact-statement execution: verify, then store and infer.

mod cache_search_proof;
mod result;
mod verify;
mod verify_atomic_fact;
mod verify_fact_result;
mod verify_obj_well_defined;
mod verify_state;

pub use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
pub use result::ExecFactStmtResult2;
pub use verify_state::VerifyState2;
