use super::evaluate_obj::evaluate_obj;
use super::helper::ActiveAlgoCalls;
use super::result::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::new_pipeline::ast::stmt::EvalStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// eval expr: display evaluation (no proof fact stored).
//
// Stages:
//   1. Substitute known_closed_numeric_equal representatives.
//   2. Recursively evaluate: closed-numeric simplify, and Identifier FnObj → algo.
//
// Example:
//   have a R = 10
//   eval a + 1
//   # → 11
//
//   algo nonzero_flag(x R) R by cases: …
//   eval nonzero_flag(0) + 1
//   # → 1
pub fn exec_eval_stmt(
    runtime: &mut Runtime,
    stmt: &EvalStmt,
) -> RuntimeResult<ExecCommandStmtResult> {
    let (rewritten_object, cited_equal_fact_ids) =
        runtime.rewrite_obj_by_known_closed_numeric_equal(&stmt.obj_to_eval);

    let mut active_calls = ActiveAlgoCalls::new();
    let evaluated_object = match evaluate_obj(runtime, &rewritten_object, 0, &mut active_calls)? {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(failed)));
        }
    };

    Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
        ExecEvalStmtSuccess {
            statement: stmt.clone(),
            source_object: stmt.obj_to_eval.clone(),
            rewritten_object,
            cited_equal_fact_ids,
            evaluated_object,
        },
    )))
}
