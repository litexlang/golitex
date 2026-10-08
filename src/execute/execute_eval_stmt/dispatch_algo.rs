use super::evaluate_closed_numeric::evaluate_closed_numeric_obj;
use super::helper::{
    algo_call_key, build_algo_param_subst, flatten_fn_obj_args, fn_obj_plain_name,
    is_number_literal, set_bound_parameter_count,
};
use super::result::ExecEvalStmtFailed;
use crate::ast::obj::{FnObj, Obj};
use crate::ast::stmt::{DefAlgoByCasesStmt, HaveFnEqualCaseByCaseStmt};
use crate::exec_env::StoredDefAlgo;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Dispatch one Identifier FnObj through a stored algo definition.
// Args must already be evaluated numeric values.
//
// Example:
//   algo nonzero_flag(x R) R by cases: case x = 0: 0 / case x != 0: 1
//   nonzero_flag(0) → return expr `0`
pub fn evaluate_fn_obj_with_algo(
    runtime: &mut Runtime,
    fn_obj: &FnObj,
    depth: usize,
    active_calls: &mut super::helper::ActiveAlgoCalls,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let Some(fn_name) = fn_obj_plain_name(fn_obj) else {
        return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression));
    };
    let raw_args = flatten_fn_obj_args(fn_obj);
    let mut normalized_args = Vec::with_capacity(raw_args.len());
    for arg in &raw_args {
        let evaluated =
            match super::evaluate_obj::evaluate_obj(runtime, arg, depth + 1, active_calls)? {
                Ok(v) => v,
                Err(failed) => return Ok(Err(failed)),
            };
        if let Some(n) = evaluate_closed_numeric_obj(&evaluated) {
            normalized_args.push(n);
        } else if is_number_literal(&evaluated) {
            normalized_args.push(evaluated);
        } else {
            return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
        }
    }

    let Some(call_key) = algo_call_key(&fn_name, &normalized_args) else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };
    if active_calls.contains(&call_key) {
        return Ok(Err(ExecEvalStmtFailed::CyclicAlgoCall));
    }
    active_calls.insert(call_key.clone());
    let outcome = (|| {
        let return_expr = match dispatch_algo_return_expr(
            runtime,
            &fn_name,
            &normalized_args,
            active_calls.function_proof_state,
        )? {
            Ok(expr) => expr,
            Err(failed) => return Ok(Err(failed)),
        };
        let definition_evidence = if active_calls.proof_mode {
            let state = &active_calls.function_proof_state;
            if !state
                .allows(crate::execute::execute_fact_stmt::VerifyStateLevel::DefinitionAndForall)
            {
                return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
            }
            let equal = crate::ast::fact::EqualFact {
                fact_id: runtime.global_ids.allocate_fact_id(),
                left: Obj::FnObj(fn_obj.clone()),
                right: return_expr.clone(),
                line_file: None,
            };
            let wd = match runtime.verify_equal_fact_well_definedness(&equal, *state)? {
                crate::execute::execute_fact_stmt::VerifyEqualFactWellDefinedResult::Success(p) => {
                    p
                }
                _ => return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed)),
            };
            let Some(searched) = runtime.search_equal_fact_proof_by_known_forall_fact(
                &equal,
                state.capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule),
            )?
            else {
                return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
            };
            super::aggregate_evaluation_result::AlgoDefinitionEvidence::Checked(
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::equal_fact_result_from_success(&equal,wd,searched))
        } else {
            super::aggregate_evaluation_result::AlgoDefinitionEvidence::Display
        };
        // Recursive proof dispatch shares the caller's search allowance. Restore
        // it for sibling terms after the returned expression has been checked.
        let caller_state = active_calls.function_proof_state.clone();
        if active_calls.proof_mode {
            active_calls.function_proof_state = caller_state
                .capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule);
        }
        let evaluated_return =
            super::evaluate_obj::evaluate_obj(runtime, &return_expr, depth + 1, active_calls);
        active_calls.function_proof_state = caller_state;
        let value = match evaluated_return? {
            Ok(v) => v,
            Err(e) => return Ok(Err(e)),
        };
        active_calls.algo_evaluations.push(
            super::aggregate_evaluation_result::AlgoApplicationEvaluationResult {
                application: Obj::FnObj(fn_obj.clone()),
                normalized_arguments: normalized_args,
                return_expression: return_expr,
                definition_evidence,
                value: value.clone(),
            },
        );
        Ok(Ok(value))
    })();
    active_calls.remove(&call_key);
    outcome
}

fn dispatch_algo_return_expr(
    runtime: &mut Runtime,
    fn_name: &str,
    evaluated_args: &[Obj],
    verify_state: VerifyState,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let Some(algo) = runtime.def_algo_visible_in_stack(fn_name).cloned() else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };
    let param_count = match &algo {
        StoredDefAlgo::ByCases(s) => {
            set_bound_parameter_count(&s.fn_set_clause.set_bound_parameters)
        }
        StoredDefAlgo::ByInduc(s) => {
            set_bound_parameter_count(&s.fn_set_clause.set_bound_parameters)
        }
    };
    if param_count != evaluated_args.len() {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    }
    dispatch_stored_algo(runtime, &algo, evaluated_args, verify_state)
}

fn dispatch_stored_algo(
    runtime: &mut Runtime,
    algo: &StoredDefAlgo,
    evaluated_args: &[Obj],
    verify_state: VerifyState,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    match algo {
        StoredDefAlgo::ByCases(stmt) => {
            dispatch_algo_by_cases(runtime, stmt, evaluated_args, verify_state)
        }
        StoredDefAlgo::ByInduc(stmt) => {
            let Some(subst) =
                build_algo_param_subst(&stmt.fn_set_clause.set_bound_parameters, evaluated_args)
            else {
                return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
            };
            match runtime.match_induc_case_body(&stmt.cases, &subst, verify_state)? {
                Some(obj) => Ok(Ok(obj)),
                None => Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed)),
            }
        }
    }
}

fn dispatch_algo_by_cases(
    runtime: &mut Runtime,
    stmt: &DefAlgoByCasesStmt,
    evaluated_args: &[Obj],
    verify_state: VerifyState,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let Some(subst) =
        build_algo_param_subst(&stmt.fn_set_clause.set_bound_parameters, evaluated_args)
    else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };
    let pseudo = HaveFnEqualCaseByCaseStmt {
        name: stmt.name.clone(),
        fn_set_clause: stmt.fn_set_clause.clone(),
        cases: stmt.cases.clone(),
        equal_tos: stmt.equal_tos.clone(),
        line_file: stmt.line_file.clone(),
    };
    match runtime.match_case_by_case_body(&pseudo, &subst, verify_state)? {
        Some((_i, body)) => Ok(Ok(body)),
        None => Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed)),
    }
}
