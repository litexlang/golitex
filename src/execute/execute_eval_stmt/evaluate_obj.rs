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
        return Ok(
            match evaluate_numeric_source(obj, active_calls.proof_mode) {
                Some(v) => Ok(v),
                None => Err(ExecEvalStmtFailed::EvaluationFailed),
            },
        );
    }

    if crate::rational_expression::contains_imaginary_unit(obj) {
        if let Some(value) = crate::rational_expression::exact_complex::exact_complex_value(obj) {
            return Ok(Ok(value));
        }
    }

    match obj {
        Obj::MatrixOperator(operator) => {
            let source_well_defined = match runtime
                .verify_obj_well_definedness(obj, active_calls.function_proof_state)?
            {
                crate::execute::execute_fact_stmt::VerifyObjWellDefinedResult::Success(p) => p,
                failed => return Ok(Err(ExecEvalStmtFailed::WellDefined(Box::new(failed)))),
            };
            let Some(expression) = runtime.matrix_scalar_definition(operator) else {
                return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression));
            };
            let value = match evaluate_obj(runtime, &expression, depth + 1, active_calls)? {
                Ok(v) => v,
                Err(e) => return Ok(Err(e)),
            };
            active_calls.matrix_scalar_evaluations.push(
                super::aggregate_evaluation_result::MatrixScalarEvaluationResult {
                    source: obj.clone(),
                    source_well_defined,
                    expression,
                    value: value.clone(),
                },
            );
            Ok(Ok(value))
        }
        Obj::ExpLogOperator(crate::ast::obj::ExpLogOperator::Sqrt(x)) => {
            let argument = match evaluate_obj(runtime, &x.arg, depth + 1, active_calls)? {
                Ok(v) => v,
                Err(e) => return Ok(Err(e)),
            };
            let expression = Obj::ExpLogOperator(crate::ast::obj::ExpLogOperator::Sqrt(
                crate::ast::obj::Sqrt {
                    arg: Box::new(argument),
                },
            ));
            Ok(
                evaluate_numeric_source(&expression, active_calls.proof_mode)
                    .ok_or(ExecEvalStmtFailed::EvaluationFailed),
            )
        }
        Obj::ComplexOperator(crate::ast::obj::ComplexOperator::Conjugate(value)) => {
            let argument = match evaluate_obj(runtime, &value.arg, depth + 1, active_calls)? {
                Ok(value) => value,
                Err(error) => return Ok(Err(error)),
            };
            let exact = Obj::ComplexOperator(crate::ast::obj::ComplexOperator::Conjugate(
                crate::ast::obj::Conjugate {
                    arg: Box::new(argument),
                },
            ));
            Ok(
                crate::rational_expression::exact_complex::exact_complex_value(&exact)
                    .map(Ok)
                    .unwrap_or(Err(ExecEvalStmtFailed::UnsupportedExpression)),
            )
        }
        Obj::ComplexOperator(operator) => {
            use crate::ast::obj::{ComplexAbs, ComplexOperator, ImaginaryPart, RealPart};
            let arg = match operator {
                ComplexOperator::ComplexAbs(x) => &x.arg,
                ComplexOperator::RealPart(x) => &x.arg,
                ComplexOperator::ImaginaryPart(x) => &x.arg,
                ComplexOperator::Conjugate(_) => unreachable!(),
            };
            let arg = match evaluate_obj(runtime, arg, depth + 1, active_calls)? {
                Ok(v) => Box::new(v),
                Err(e) => return Ok(Err(e)),
            };
            let expression = Obj::ComplexOperator(match operator {
                ComplexOperator::ComplexAbs(_) => ComplexOperator::ComplexAbs(ComplexAbs { arg }),
                ComplexOperator::RealPart(_) => ComplexOperator::RealPart(RealPart { arg }),
                ComplexOperator::ImaginaryPart(_) => {
                    ComplexOperator::ImaginaryPart(ImaginaryPart { arg })
                }
                ComplexOperator::Conjugate(_) => unreachable!(),
            });
            let value = crate::rational_expression::exact_rational::evaluate_obj_to_exact_rational_obj_for_eval(&expression)
                .or_else(|| crate::rational_expression::exact_complex::exact_modulus_value(&expression));
            Ok(match value {
                Some(value) => Ok(
                    crate::rational_expression::exact_radical::ExactRadical::from_obj(&value)
                        .map(|normal| normal.to_obj())
                        .unwrap_or(value),
                ),
                None => Err(ExecEvalStmtFailed::UnsupportedExpression),
            })
        }
        Obj::FiniteSetStat(_) | Obj::ProductShape(_) => {
            super::evaluate_finite_objects::evaluate_finite_object(
                runtime,
                obj,
                depth,
                active_calls,
            )
        }
        Obj::ArithmeticOperator(op) => {
            evaluate_arithmetic_operator(runtime, op, depth, active_calls)
        }
        Obj::IteratedOperator(op) => {
            super::evaluate_aggregate::evaluate_aggregate(runtime, op, depth, active_calls)
        }
        Obj::FnObj(fn_obj) => {
            use super::aggregate_evaluation_result::{
                CheckedBetaFunctionApplicationExpansionProof, FunctionApplicationExpansionProof,
            };
            let application_well_defined = match runtime
                .verify_obj_well_definedness(obj, active_calls.function_proof_state)?
            {
                crate::execute::execute_fact_stmt::VerifyObjWellDefinedResult::Success(p) => p,
                failed => return Ok(Err(ExecEvalStmtFailed::WellDefined(Box::new(failed)))),
            };
            let expansion = if let Some(proof) =
                runtime.expanded_named_or_literal_anon_fn_application_body(fn_obj)?
            {
                Some(FunctionApplicationExpansionProof::Anonymous(proof))
            } else {
                runtime
                    .parent_checked_beta_body(
                        obj,
                        &application_well_defined,
                        active_calls.function_proof_state,
                    )?
                    .map(|(function_body, expanded_body)| {
                        FunctionApplicationExpansionProof::CheckedBeta(
                            CheckedBetaFunctionApplicationExpansionProof {
                                function_body,
                                expanded_body,
                            },
                        )
                    })
            };
            if let Some(expansion) = expansion {
                let (body, cites) =
                    runtime.rewrite_obj_by_known_closed_numeric_equal(expansion.expanded_body());
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
    Ok(
        match evaluate_numeric_source(&combined, active_calls.proof_mode) {
            Some(v) => Ok(v),
            None => Err(ExecEvalStmtFailed::EvaluationFailed),
        },
    )
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
    Ok(
        match evaluate_numeric_source(&combined, active_calls.proof_mode) {
            Some(v) => Ok(v),
            None => Err(ExecEvalStmtFailed::EvaluationFailed),
        },
    )
}

// Mathematical proof evaluation cannot turn a display-only decimal
// approximation (or an overflowing exact operation) into an equality witness.
// Ordinary `eval` keeps its existing display behavior.
pub(super) fn evaluate_numeric_source(obj: &Obj, proof_mode: bool) -> Option<Obj> {
    if crate::rational_expression::contains_imaginary_unit(obj) {
        if let Some(value) = crate::rational_expression::exact_complex::exact_complex_value(obj) {
            return Some(value);
        }
    }
    if proof_mode {
        crate::rational_expression::exact_rational::evaluate_obj_to_exact_rational_obj_for_eval(obj)
            .or_else(|| {
                crate::rational_expression::exact_radical::ExactRadical::from_obj(obj)
                    .map(|x| x.to_obj())
            })
    } else {
        evaluate_closed_numeric_obj(obj)
    }
}

#[cfg(test)]
mod matrix_exact_evaluation_tests {
    use super::*;
    use crate::ast::obj::{Literal, Number};

    fn number(n: &str) -> Obj {
        Obj::Literal(Literal::Number(Number::new(n.into())))
    }

    #[test]
    fn native_matrix_proof_evaluation_declines_decimal_and_overflow_fallbacks() {
        let exponent = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: Box::new(number("1")),
            right: Box::new(number("3")),
        }));
        let cube_root = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(number("2")),
            exponent: Box::new(exponent),
        }));
        assert!(evaluate_numeric_source(&cube_root, true).is_none());
        assert_eq!(
            evaluate_numeric_source(&cube_root, false),
            evaluate_closed_numeric_obj(&cube_root)
        );
        let overflow = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(number(&i128::MAX.to_string())),
            right: Box::new(number("2")),
        }));
        assert!(evaluate_numeric_source(&overflow, true).is_none());
        assert_eq!(
            evaluate_numeric_source(&overflow, false),
            evaluate_closed_numeric_obj(&overflow)
        );
    }
}
