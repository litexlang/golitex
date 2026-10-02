use super::dispatch_algo::evaluate_fn_obj_with_algo;
use super::evaluate_closed_numeric::evaluate_closed_numeric_obj;
use super::helper::{ActiveAlgoCalls, MAX_EVAL_DEPTH};
use super::result::ExecEvalStmtFailed;
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Ceil, Div, Floor, Max, Min, Mul, Neg, Obj, Pow, Sign, Sub,
};
use crate::rational_expression::ClosedNumericExpr;
use crate::runtime::{Runtime, RuntimeResult};

// Recursive display evaluation after closed-numeric equal rewrite.
//
// Supported residual shapes:
// - ClosedNumericExpr → exact/decimal simplify
// - ArithmeticOperator whose children evaluate → rebuild → simplify
// - FnObj with plain Identifier head + stored algo → dispatch → recurse
//
// Example: `nonzero_flag(0) + 1` → `0 + 1` → `1`
pub fn evaluate_obj(
    runtime: &mut Runtime,
    obj: &Obj,
    depth: usize,
    active_calls: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    if depth > MAX_EVAL_DEPTH {
        return Ok(Err(ExecEvalStmtFailed::DepthExceeded));
    }

    if ClosedNumericExpr::try_from_obj(obj).is_some() {
        return Ok(match evaluate_closed_numeric_obj(obj) {
            Some(v) => Ok(v),
            None => Err(ExecEvalStmtFailed::EvaluationFailed),
        });
    }

    match obj {
        Obj::FiniteSetStat(_) | Obj::ProductShape(_) => super::evaluate_finite_objects::evaluate_finite_object(runtime,obj,depth,active_calls),
        Obj::ArithmeticOperator(op) => {
            evaluate_arithmetic_operator(runtime, op, depth, active_calls)
        }
        Obj::IteratedOperator(op) => {
            super::evaluate_aggregate::evaluate_aggregate(runtime, op, depth, active_calls)
        }
        Obj::FnObj(fn_obj) => {
            if let Some(expansion) =
                runtime.expanded_named_or_literal_anon_fn_application_body(fn_obj)?
            {
                let application_well_defined = match runtime.verify_obj_well_definedness(
                    obj,
                    crate::execute::execute_by_stmt::proof_verify_state()
                        .without_well_defined_storage(),
                )? {
                    crate::execute::execute_fact_stmt::VerifyObjWellDefinedResult::Success(p) => p,
                    failed => return Ok(Err(ExecEvalStmtFailed::WellDefined(Box::new(failed)))),
                };
                let (body, cites) =
                    runtime.rewrite_obj_by_known_closed_numeric_equal(&expansion.expanded_body);
                active_calls.cited_equal_fact_ids.extend(cites);
                let value = match evaluate_obj(runtime, &body, depth + 1, active_calls)? {
                    Ok(v) => v,
                    Err(e) => return Ok(Err(e)),
                };
                active_calls.function_evaluations.push(
                    super::aggregate_evaluation_result::FunctionApplicationEvaluationResult {
                        application: obj.clone(),
                        application_well_defined,
                        expansion,
                        value: value.clone(),
                    },
                );
                Ok(Ok(value))
            } else {
                evaluate_fn_obj_with_algo(runtime, fn_obj, depth, active_calls)
            }
        }
        _ => Ok(Err(ExecEvalStmtFailed::UnsupportedExpression)),
    }
}

fn evaluate_arithmetic_operator(
    runtime: &mut Runtime,
    op: &ArithmeticOperator,
    depth: usize,
    active_calls: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    match op {
        ArithmeticOperator::Add(a) => {
            eval_bin(runtime, &a.left, &a.right, depth, active_calls, |l, r| {
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: Box::new(l),
                    right: Box::new(r),
                }))
            })
        }
        ArithmeticOperator::Sub(a) => {
            eval_bin(runtime, &a.left, &a.right, depth, active_calls, |l, r| {
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                    left: Box::new(l),
                    right: Box::new(r),
                }))
            })
        }
        ArithmeticOperator::Mul(a) => {
            eval_bin(runtime, &a.left, &a.right, depth, active_calls, |l, r| {
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: Box::new(l),
                    right: Box::new(r),
                }))
            })
        }
        ArithmeticOperator::Div(a) => {
            eval_bin(runtime, &a.left, &a.right, depth, active_calls, |l, r| {
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: Box::new(l),
                    right: Box::new(r),
                }))
            })
        }
        ArithmeticOperator::Min(a) => {
            eval_bin(runtime, &a.left, &a.right, depth, active_calls, |l, r| {
                Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
                    left: Box::new(l),
                    right: Box::new(r),
                }))
            })
        }
        ArithmeticOperator::Max(a) => {
            eval_bin(runtime, &a.left, &a.right, depth, active_calls, |l, r| {
                Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                    left: Box::new(l),
                    right: Box::new(r),
                }))
            })
        }
        ArithmeticOperator::Pow(a) => eval_bin(
            runtime,
            &a.base,
            &a.exponent,
            depth,
            active_calls,
            |l, r| {
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                    base: Box::new(l),
                    exponent: Box::new(r),
                }))
            },
        ),
        ArithmeticOperator::Neg(a) => eval_un(runtime, &a.arg, depth, active_calls, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(arg) }))
        }),
        ArithmeticOperator::Abs(a) => eval_un(runtime, &a.arg, depth, active_calls, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: Box::new(arg) }))
        }),
        ArithmeticOperator::Floor(a) => eval_un(runtime, &a.arg, depth, active_calls, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor { arg: Box::new(arg) }))
        }),
        ArithmeticOperator::Ceil(a) => eval_un(runtime, &a.arg, depth, active_calls, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(Ceil { arg: Box::new(arg) }))
        }),
        ArithmeticOperator::Sign(a) => eval_un(runtime, &a.arg, depth, active_calls, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign { arg: Box::new(arg) }))
        }),
    }
}

fn eval_bin<F>(
    runtime: &mut Runtime,
    left: &Obj,
    right: &Obj,
    depth: usize,
    active_calls: &mut ActiveAlgoCalls,
    rebuild: F,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>>
where
    F: FnOnce(Obj, Obj) -> Obj,
{
    let left_v = match evaluate_obj(runtime, left, depth + 1, active_calls)? {
        Ok(v) => v,
        Err(failed) => return Ok(Err(failed)),
    };
    let right_v = match evaluate_obj(runtime, right, depth + 1, active_calls)? {
        Ok(v) => v,
        Err(failed) => return Ok(Err(failed)),
    };
    let combined = rebuild(left_v, right_v);
    Ok(match evaluate_closed_numeric_obj(&combined) {
        Some(v) => Ok(v),
        None => Err(ExecEvalStmtFailed::EvaluationFailed),
    })
}

fn eval_un<F>(
    runtime: &mut Runtime,
    arg: &Obj,
    depth: usize,
    active_calls: &mut ActiveAlgoCalls,
    rebuild: F,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>>
where
    F: FnOnce(Obj) -> Obj,
{
    let arg_v = match evaluate_obj(runtime, arg, depth + 1, active_calls)? {
        Ok(v) => v,
        Err(failed) => return Ok(Err(failed)),
    };
    let combined = rebuild(arg_v);
    Ok(match evaluate_closed_numeric_obj(&combined) {
        Some(v) => Ok(v),
        None => Err(ExecEvalStmtFailed::EvaluationFailed),
    })
}
