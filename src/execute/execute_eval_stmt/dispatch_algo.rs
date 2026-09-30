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
use super::evaluate_closed_numeric::evaluate_closed_numeric_obj;

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
        let evaluated = match super::evaluate_obj::evaluate_obj(runtime, arg, depth + 1, active_calls)?
        {
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

    let return_expr =
        match dispatch_algo_return_expr(runtime, &fn_name, &normalized_args, active_calls)? {
            Ok(expr) => expr,
            Err(failed) => return Ok(Err(failed)),
        };
    super::evaluate_obj::evaluate_obj(runtime, &return_expr, depth + 1, active_calls)
}

fn dispatch_algo_return_expr(
    runtime: &mut Runtime,
    fn_name: &str,
    evaluated_args: &[Obj],
    active_calls: &mut super::helper::ActiveAlgoCalls,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let Some(algo) = runtime.def_algo_visible_in_stack(fn_name).cloned() else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };
    let param_count = match &algo {
        StoredDefAlgo::ByCases(s) => set_bound_parameter_count(&s.fn_set_clause.set_bound_parameters),
        StoredDefAlgo::ByInduc(s) => set_bound_parameter_count(&s.fn_set_clause.set_bound_parameters),
    };
    if param_count != evaluated_args.len() {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    }
    let Some(call_key) = algo_call_key(fn_name, evaluated_args) else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };
    if active_calls.contains(&call_key) {
        return Ok(Err(ExecEvalStmtFailed::CyclicAlgoCall));
    }
    active_calls.insert(call_key.clone());
    let outcome = dispatch_stored_algo(runtime, &algo, evaluated_args);
    active_calls.remove(&call_key);
    outcome
}

fn dispatch_stored_algo(
    runtime: &mut Runtime,
    algo: &StoredDefAlgo,
    evaluated_args: &[Obj],
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let verify_state = VerifyState {
            can_use_builtin_rule_round: VerifyState::TOP_BUILTIN_RULE_ROUND,
        can_use_def_and_known_forall_and_known_strategy: true,
        can_use_rewrite: true,
        store_well_defined_fact: false,
};
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
