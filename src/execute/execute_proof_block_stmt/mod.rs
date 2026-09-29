//! ProofBlock stmt execution: `claim` / `sketch`.

mod exec_claim_stmt;
mod exec_sketch_stmt;
mod helper;
mod result;

pub(in crate::execute) use exec_claim_stmt::exec_claim_stmt;
pub(in crate::execute) use exec_sketch_stmt::exec_sketch_stmt;
pub(in crate::execute) use helper::run_proof_body_stmts;
pub use result::{
    ExecClaimStmtFailed, ExecClaimStmtResult, ExecClaimStmtSuccess, ExecProofBlockStmtResult,
    ExecSketchStmtFailed, ExecSketchStmtResult, ExecSketchStmtSuccess, ProofBlockBodyFailed,
};
