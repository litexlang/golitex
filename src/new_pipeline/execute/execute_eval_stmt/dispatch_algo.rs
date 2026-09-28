use super::evaluate_closed_numeric::evaluate_closed_numeric_obj;
use super::helper::{
    algo_call_key, build_algo_param_subst, flatten_fn_obj_args, fn_obj_plain_name, ActiveAlgoCalls,
};
use super::result::ExecEvalStmtFailed;
use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::DefAlgoStmt;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Dispatch one Identifier FnObj through a stored DefAlgoStmt.
// Args must already be evaluated values (typically number literals).
// Returns the instantiated return expression (not yet recursively evaluated).
//
// Example:
//   have algo for fn nonzero_flag(x): case x = 0: 0 / case x != 0: 1
//   nonzero_flag(0) → return expr `0`
pub fn dispatch_algo_return_expr(
    runtime: &mut Runtime,
    fn_name: &str,
    evaluated_args: &[Obj],
    active_calls: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let Some(algo) = runtime.def_algo_visible_in_stack(fn_name).cloned() else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };
    if algo.param_bindings.len() != evaluated_args.len() {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    }
    let Some(call_key) = algo_call_key(fn_name, evaluated_args) else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };
    if active_calls.contains(&call_key) {
        return Ok(Err(ExecEvalStmtFailed::CyclicAlgoCall));
    }
    active_calls.insert(call_key.clone());
    let outcome = dispatch_algo_cases(runtime, &algo, evaluated_args);
    active_calls.remove(&call_key);
    outcome
}

fn dispatch_algo_cases(
    runtime: &mut Runtime,
    algo: &DefAlgoStmt,
    evaluated_args: &[Obj],
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let Some(subst) = build_algo_param_subst(algo, evaluated_args) else {
        return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
    };

    let verify_state = VerifyState {
        can_use_forall_fact: true,
        can_use_rewrite: true,
        store_well_defined_fact: false,
    };

    for case in &algo.cases {
        let condition = match runtime.inst_atomic_fact(&case.condition, &subst) {
            Ok(c) => c,
            Err(_) => return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed)),
        };
        let proof = runtime.verify_atomic_fact(&condition, verify_state.clone())?;
        if proof.is_failed() {
            continue;
        }
        return match runtime.inst_obj(&case.return_stmt.value, &subst) {
            Ok(obj) => Ok(Ok(obj)),
            Err(_) => Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed)),
        };
    }

    if let Some(default_return) = &algo.default_return {
        return match runtime.inst_obj(&default_return.value, &subst) {
            Ok(obj) => Ok(Ok(obj)),
            Err(_) => Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed)),
        };
    }

    // Silence unused import if AtomicFact only used via case.condition type.
    let _ = std::any::type_name::<AtomicFact>();
    Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed))
}

// Evaluate FnObj: require plain Identifier head + stored algo.
pub fn evaluate_fn_obj_with_algo(
    runtime: &mut Runtime,
    fn_obj: &crate::new_pipeline::ast::obj::FnObj,
    depth: usize,
    active_calls: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let Some(fn_name) = fn_obj_plain_name(fn_obj) else {
        return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression));
    };
    let raw_args = flatten_fn_obj_args(fn_obj);
    let mut evaluated_args = Vec::with_capacity(raw_args.len());
    for arg in &raw_args {
        match super::evaluate_obj::evaluate_obj(runtime, arg, depth + 1, active_calls)? {
            Ok(v) => evaluated_args.push(v),
            Err(failed) => return Ok(Err(failed)),
        }
    }
    // This knife: args should land on concrete numeric values.
    for arg in &evaluated_args {
        if evaluate_closed_numeric_obj(arg).is_none() && !super::helper::is_number_literal(arg) {
            // Allow already-normalized number literals; otherwise require closed eval.
            if evaluate_closed_numeric_obj(arg).is_none() {
                return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
            }
        }
    }
    // Normalize args to simplified numeric objs when possible.
    let mut normalized_args = Vec::with_capacity(evaluated_args.len());
    for arg in evaluated_args {
        if let Some(n) = evaluate_closed_numeric_obj(&arg) {
            normalized_args.push(n);
        } else if super::helper::is_number_literal(&arg) {
            normalized_args.push(arg);
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
