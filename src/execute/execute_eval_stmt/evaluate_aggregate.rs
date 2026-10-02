use super::aggregate_evaluation_result::*;
use super::evaluate_closed_numeric::evaluate_closed_numeric_obj;
use super::evaluate_obj::evaluate_obj;
use super::helper::{ActiveAlgoCalls, MAX_AGGREGATE_TERMS};
use super::result::ExecEvalStmtFailed;
use crate::ast::obj::{FnObj, FnObjHead, FunctionSpace, IteratedOperator, Literal, Number, Obj, SetFormer};
use crate::execute::execute_by_stmt::proof_verify_state;
use crate::execute::execute_fact_stmt::VerifyObjWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::helper::{add_objs, mul_objs};
use crate::runtime::{Runtime, RuntimeResult};

pub fn evaluate_aggregate(
    runtime: &mut Runtime,
    op: &IteratedOperator,
    depth: usize,
    context: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<Obj, ExecEvalStmtFailed>> {
    let source = Obj::IteratedOperator(op.clone());
    macro_rules! checked {
        ($e:expr) => {
            match $e? {
                Ok(v) => v,
                Err(e) => return Ok(Err(e)),
            }
        };
    }
    let (proof, value) = match op {
        IteratedOperator::Sum(s) => {
            let bounds = checked!(evaluate_bounds(runtime, &s.start, &s.end, depth, context));
            let indices = checked!(enumerate_range(
                bounds.start_integer,
                bounds.end_integer,
                false,
                context
            ));
            let (terms, value) = checked!(evaluate_terms(
                runtime, &s.func, indices, false, depth, context
            ));
            (
                AggregateEvaluationResult::Sum(RangeSumEvaluationResult {
                    source,
                    bounds,
                    terms,
                    value: value.clone(),
                }),
                value,
            )
        }
        IteratedOperator::SumOfFiniteSet(s) => {
            let enumeration = checked!(enumerate_set(runtime, &s.set, depth, context));
            let (terms, value) = checked!(evaluate_terms(
                runtime,
                &s.func,
                enumeration.elements.clone(),
                false,
                depth,
                context
            ));
            (
                AggregateEvaluationResult::SumOfFiniteSet(FiniteSetSumEvaluationResult {
                    source,
                    enumeration,
                    terms,
                    value: value.clone(),
                }),
                value,
            )
        }
        IteratedOperator::Product(s) => {
            let bounds = checked!(evaluate_bounds(runtime, &s.start, &s.end, depth, context));
            let indices = checked!(enumerate_range(
                bounds.start_integer,
                bounds.end_integer,
                false,
                context
            ));
            let (terms, value) = checked!(evaluate_terms(
                runtime, &s.func, indices, true, depth, context
            ));
            (
                AggregateEvaluationResult::Product(RangeProductEvaluationResult {
                    source,
                    bounds,
                    terms,
                    value: value.clone(),
                }),
                value,
            )
        }
        IteratedOperator::ProductOfFiniteSet(s) => {
            let enumeration = checked!(enumerate_set(runtime, &s.set, depth, context));
            let (terms, value) = checked!(evaluate_terms(
                runtime,
                &s.func,
                enumeration.elements.clone(),
                true,
                depth,
                context
            ));
            (
                AggregateEvaluationResult::ProductOfFiniteSet(FiniteSetProductEvaluationResult {
                    source,
                    enumeration,
                    terms,
                    value: value.clone(),
                }),
                value,
            )
        }
        IteratedOperator::Reduce(_) | IteratedOperator::FiniteSetReduce(_) => {
            return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression));
        }
    };
    context.aggregate_evaluations.push(proof);
    Ok(Ok(value))
}

fn evaluate_bounds(
    runtime: &mut Runtime,
    start: &Obj,
    end: &Obj,
    depth: usize,
    context: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<AggregateRangeBoundsResult, ExecEvalStmtFailed>> {
    let (start, mut cited_equal_fact_ids) =
        runtime.rewrite_obj_by_known_closed_numeric_equal(start);
    let (end, end_cites) = runtime.rewrite_obj_by_known_closed_numeric_equal(end);
    cited_equal_fact_ids.extend(end_cites);
    let start = match evaluate_obj(runtime, &start, depth + 1, context)? {
        Ok(v) => v,
        Err(e) => return Ok(Err(e)),
    };
    let end = match evaluate_obj(runtime, &end, depth + 1, context)? {
        Ok(v) => v,
        Err(e) => return Ok(Err(e)),
    };
    let integers = EvalRational::from_obj(&start)
        .and_then(|n| n.to_i128_if_integer())
        .zip(EvalRational::from_obj(&end).and_then(|n| n.to_i128_if_integer()));
    let Some((start_integer, end_integer)) = integers else {
        return Ok(Err(ExecEvalStmtFailed::AggregateRangeOverflow));
    };
    Ok(Ok(AggregateRangeBoundsResult {
        start,
        end,
        cited_equal_fact_ids,
        start_integer,
        end_integer,
    }))
}

fn enumerate_range(
    start: i128,
    end: i128,
    allow_empty: bool,
    context: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<Vec<Obj>, ExecEvalStmtFailed>> {
    if end < start {
        return Ok(if allow_empty {
            Ok(vec![])
        } else {
            Err(ExecEvalStmtFailed::EvaluationFailed)
        });
    }
    let Some(count) = end
        .checked_sub(start)
        .and_then(|n| n.checked_add(1))
        .and_then(|n| usize::try_from(n).ok())
    else {
        return Ok(Err(ExecEvalStmtFailed::AggregateRangeOverflow));
    };
    if count > context.aggregate_terms_remaining {
        return Ok(Err(ExecEvalStmtFailed::AggregateBudgetExceeded));
    }
    context.aggregate_terms_remaining -= count;
    let mut result = Vec::with_capacity(count);
    let mut index = start;
    for position in 0..count {
        result.push(Obj::Literal(Literal::Number(Number::new(
            index.to_string(),
        ))));
        if position + 1 < count {
            let Some(next) = index.checked_add(1) else {
                return Ok(Err(ExecEvalStmtFailed::AggregateRangeOverflow));
            };
            index = next;
        }
    }
    Ok(Ok(result))
}

fn enumerate_set(
    runtime: &mut Runtime,
    set: &Obj,
    depth: usize,
    context: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<FiniteSetEnumerationResult, ExecEvalStmtFailed>> {
    let members = equivalence_class_members_with_paths_in_adjacency(
        &runtime.visible_equivalence_class_adjacency(),
        set,
    );
    for (candidate, path) in members {
        let mut cites = Vec::new();
        let elements = match &candidate {
            Obj::SetFormer(SetFormer::ListSet(list)) => {
                if list.list.len() > MAX_AGGREGATE_TERMS
                    || list.list.len() > context.aggregate_terms_remaining
                {
                    return Ok(Err(ExecEvalStmtFailed::AggregateBudgetExceeded));
                }
                let mut elements = Vec::new();
                for raw in &list.list {
                    let (rewritten, ids) = runtime.rewrite_obj_by_known_closed_numeric_equal(raw);
                    cites.extend(ids);
                    let value = match evaluate_obj(runtime, &rewritten, depth + 1, context)? {
                        Ok(v) => v,
                        Err(e) => return Ok(Err(e)),
                    };
                    // Values are exact canonical numeric objects. Sets do not
                    // repeat a value even if its input spellings differ.
                    if !elements.iter().any(|v: &Obj| v.ir() == value.ir()) {
                        elements.push(value);
                    }
                }
                if elements.len() > context.aggregate_terms_remaining {
                    return Ok(Err(ExecEvalStmtFailed::AggregateBudgetExceeded));
                }
                context.aggregate_terms_remaining -= elements.len();
                elements
            }
            Obj::SetFormer(SetFormer::ClosedRange(range)) => {
                let bounds =
                    match evaluate_bounds(runtime, &range.start, &range.end, depth, context)? {
                        Ok(v) => v,
                        Err(e) => return Ok(Err(e)),
                    };
                cites.extend(bounds.cited_equal_fact_ids);
                match enumerate_range(bounds.start_integer, bounds.end_integer, true, context)? {
                    Ok(v) => v,
                    Err(e) => return Ok(Err(e)),
                }
            }
            Obj::SetFormer(SetFormer::Range(range)) => {
                let bounds =
                    match evaluate_bounds(runtime, &range.start, &range.end, depth, context)? {
                        Ok(v) => v,
                        Err(e) => return Ok(Err(e)),
                    };
                cites.extend(bounds.cited_equal_fact_ids);
                if bounds.end_integer <= bounds.start_integer {
                    vec![]
                } else {
                    match enumerate_range(
                        bounds.start_integer,
                        bounds.end_integer - 1,
                        true,
                        context,
                    )? {
                        Ok(v) => v,
                        Err(e) => return Ok(Err(e)),
                    }
                }
            }
            _ => continue,
        };
        return Ok(Ok(FiniteSetEnumerationResult {
            set_equality: KnownEqualityPathProof::new(path),
            resolved_set: candidate,
            cited_equal_fact_ids: cites,
            elements,
        }));
    }
    Ok(Err(ExecEvalStmtFailed::UnsupportedExpression))
}

fn evaluate_terms(
    runtime: &mut Runtime,
    function: &Obj,
    indices: Vec<Obj>,
    product: bool,
    depth: usize,
    context: &mut ActiveAlgoCalls,
) -> RuntimeResult<Result<(Vec<AggregateTermEvaluationResult>, Obj), ExecEvalStmtFailed>> {
    let mut accumulated = Obj::Literal(Literal::Number(Number::new(
        if product { "1" } else { "0" }.into(),
    )));
    let mut terms = Vec::with_capacity(indices.len());
    for argument in indices {
        let Some(application) = unary_application(function, argument.clone()) else {
            return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression));
        };
        let application_well_defined = match runtime.verify_obj_well_definedness(
            &Obj::FnObj(application.clone()),
            proof_verify_state().without_well_defined_storage(),
        )? {
            VerifyObjWellDefinedResult::Success(p) => p,
            failed => return Ok(Err(ExecEvalStmtFailed::WellDefined(Box::new(failed)))),
        };
        let nested_start = context.aggregate_evaluations.len();
        let (expansion, value) = if let Some(expansion) =
            runtime.expanded_named_or_literal_anon_fn_application_body(&application)?
        {
            let (body, cites) =
                runtime.rewrite_obj_by_known_closed_numeric_equal(&expansion.expanded_body);
            context.cited_equal_fact_ids.extend(cites);
            let value = match evaluate_obj(runtime, &body, depth + 1, context)? {
                Ok(v) => v,
                Err(e) => return Ok(Err(e)),
            };
            (AggregateTermExpansion::Function(expansion), value)
        } else {
            let value = match super::dispatch_algo::evaluate_fn_obj_with_algo(
                runtime,
                &application,
                depth + 1,
                context,
            )? {
                Ok(v) => v,
                Err(e) => return Ok(Err(e)),
            };
            (
                AggregateTermExpansion::Algorithm {
                    evaluation_index: context.algo_evaluations.len() - 1,
                },
                value,
            )
        };
        let combined = if product {
            mul_objs(accumulated, value.clone())
        } else {
            add_objs(accumulated, value.clone())
        };
        let Some(next) = evaluate_closed_numeric_obj(&combined) else {
            return Ok(Err(ExecEvalStmtFailed::EvaluationFailed));
        };
        accumulated = next;
        terms.push(AggregateTermEvaluationResult {
            argument,
            application: Obj::FnObj(application),
            application_well_defined,
            expansion,
            nested_aggregate_evidence: nested_start..context.aggregate_evaluations.len(),
            value,
            accumulated_value: accumulated.clone(),
        });
    }
    Ok(Ok((terms, accumulated)))
}

pub(in crate::execute) fn unary_application(function: &Obj, argument: Obj) -> Option<FnObj> {
    match function {
        Obj::Identifier(id) => Some(FnObj {
            head: Box::new(FnObjHead::Identifier(id.clone())),
            body: vec![vec![Box::new(argument)]],
        }),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => Some(FnObj {
            head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()))),
            body: vec![vec![Box::new(argument)]],
        }),
        Obj::FnObj(call) => {
            let mut call = call.clone();
            call.body.push(vec![Box::new(argument)]);
            Some(call)
        }
        _ => None,
    }
}
