use super::evaluate_obj::evaluate_obj;
use super::helper::ActiveAlgoCalls;
use super::result::{ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::ast::stmt::EvalStmt;
use crate::execute::execute_by_stmt::proof_verify_state;
use crate::execute::execute_fact_stmt::VerifyObjWellDefinedResult;
use crate::runtime::{Runtime, RuntimeResult};

// eval expr: display evaluation (no proof fact stored).
//
// Stages:
//   1. Check the source expression's WD, including callable domains.
//   2. Substitute known_closed_numeric_equal representatives.
//   3. Recursively evaluate: closed-numeric simplify, and Identifier FnObj → algo.
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
    let source_well_defined = match runtime
        .verify_obj_well_definedness(&stmt.obj_to_eval, proof_verify_state())?
    {
        VerifyObjWellDefinedResult::Success(proof) => proof,
        failed => {
            return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
                ExecEvalStmtFailed::WellDefined(Box::new(failed)),
            )));
        }
    };
    let (rewritten_object, mut cited_equal_fact_ids) =
        runtime.rewrite_obj_by_known_closed_numeric_equal(&stmt.obj_to_eval);

    let mut active_calls = ActiveAlgoCalls::new();
    let evaluated_object = match evaluate_obj(runtime, &rewritten_object, 0, &mut active_calls)? {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(failed)));
        }
    };

    cited_equal_fact_ids.extend(active_calls.cited_equal_fact_ids);

    Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
        ExecEvalStmtSuccess {
            statement: stmt.clone(),
            source_object: stmt.obj_to_eval.clone(),
            source_well_defined,
            rewritten_object,
            cited_equal_fact_ids,
            evaluated_object,
            aggregate_evaluations: active_calls.aggregate_evaluations,
            function_evaluations: active_calls.function_evaluations,
            algo_evaluations: active_calls.algo_evaluations,
        },
    )))
}
