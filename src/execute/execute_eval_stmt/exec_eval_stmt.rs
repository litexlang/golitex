use super::evaluate_obj::evaluate_obj;
use super::helper::ActiveAlgoCalls;
use super::result::{
    ExecCommandStmtResult, ExecEvalStmtFailed, ExecEvalStmtResult, ExecEvalStmtSuccess,
};
use super::verify_evaluated_algo_calls::verify_evaluated_algo_calls;
use crate::ast::fact::{EqualFact, Fact};
use crate::ast::stmt::EvalStmt;
use crate::execute::execute_by_stmt::proof_verify_state;
use crate::execute::execute_fact_stmt::{
    VerifyEqualFactWellDefinedResult, VerifyObjWellDefinedResult,
};
use crate::runtime::{Runtime, RuntimeResult};

// eval expr: compute an exact value, certify algorithm equations, then publish
// expr = value through the same store/infer and exec_stmt transaction as facts.
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
    let source_well_defined =
        match runtime.verify_obj_well_definedness(&stmt.obj_to_eval, proof_verify_state())? {
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
            // A proved numeric modulus may rewrite to its exact, nonfoldable
            // principal root. Preserve that computed display value, rather than
            // make eval depend on whether its equality was asserted earlier.
            // Example: C_abs(1+i)=sqrt(2); eval C_abs(1+i) still displays sqrt(2).
            let modulus_value = match failed {
                ExecEvalStmtFailed::UnsupportedExpression
                | ExecEvalStmtFailed::EvaluationFailed => {
                    crate::rational_expression::exact_complex::exact_modulus_value(
                        &stmt.obj_to_eval,
                    )
                }
                _ => None,
            };
            match modulus_value {
                Some(value)
                    if crate::rational_expression::objs_equal_by_rational_expression_evaluation(
                        &value,
                        &rewritten_object,
                    ) =>
                {
                    value
                }
                _ => {
                    return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
                        failed,
                    )))
                }
            }
        }
    };

    cited_equal_fact_ids.extend(active_calls.cited_equal_fact_ids);

    if let Err(failed) = verify_evaluated_algo_calls(runtime, &mut active_calls.algo_evaluations)? {
        return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
            failed,
        )));
    }
    let evaluated_equal_fact = EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: stmt.obj_to_eval.clone(),
        right: evaluated_object.clone(),
        line_file: Some(stmt.line_file.clone()),
    };
    let evaluated_equal_well_defined = match runtime
        .verify_equal_fact_well_definedness(&evaluated_equal_fact, proof_verify_state())?
    {
        VerifyEqualFactWellDefinedResult::Success(proof) => proof,
        failed => {
            return Ok(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(
                ExecEvalStmtFailed::EvaluatedEqualityWellDefined(Box::new(failed)),
            )))
        }
    };
    // The exact computation and checked defining equations above establish the
    // equality. Do not re-run automatic equality search to rediscover that trace.
    let fact: Fact = evaluated_equal_fact.clone().into();
    let store_and_infer_result = runtime.store_fact_and_infer(&fact, proof_verify_state())?;

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
            evaluated_equal_fact,
            evaluated_equal_well_defined,
            store_and_infer_result,
        },
    )))
}
