use super::helper::run_proof_body_stmts;
use super::result::{
    ExecProofBlockStmtResult, ExecSketchStmtFailed, ExecSketchStmtResult, ExecSketchStmtSuccess,
};
use crate::ast::stmt::SketchStmt;
use crate::runtime::{Runtime, RuntimeResult};

// sketch: check body stmts in a child scope; store nothing outside.
//
// Condition: every body stmt succeeds (soft-fail → whole sketch Failed).
// After: no facts or defs escape the discarded local_env.
//
// Example:
//   sketch:
//       1 = 1
pub fn exec_sketch_stmt(
    runtime: &mut Runtime,
    stmt: &SketchStmt,
) -> RuntimeResult<ExecProofBlockStmtResult> {
    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        match run_proof_body_stmts(rt, &stmt.proof)? {
            Ok(steps) => Ok(Ok(steps)),
            Err(failed) => Ok(Err(ExecSketchStmtFailed::ProofBody(failed))),
        }
    })?;


    match local_outcome {
        Ok(proof_steps) => Ok(ExecProofBlockStmtResult::Sketch(
            ExecSketchStmtResult::Success(ExecSketchStmtSuccess {
                proof_steps,
                local_env,
            }),
        )),
        Err(failed) => Ok(ExecProofBlockStmtResult::Sketch(
            ExecSketchStmtResult::Failed(failed),
        )),
    }
}
