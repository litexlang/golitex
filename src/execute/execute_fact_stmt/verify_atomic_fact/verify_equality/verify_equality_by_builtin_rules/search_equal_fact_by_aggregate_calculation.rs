use crate::ast::fact::EqualFact;
use crate::ast::obj::{ArithmeticOperator, IteratedOperator, Obj};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AlgoApplicationEvaluationResult;
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    AggregateEvaluationResult, FunctionApplicationEvaluationResult,
};
use crate::execute::execute_eval_stmt::evaluate_obj::evaluate_obj;
use crate::execute::execute_eval_stmt::helper::ActiveAlgoCalls;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;
use crate::runtime::{FactId, Runtime, RuntimeResult};

pub struct AggregateCalculationBuiltinRuleProof {
    pub rewritten_left: Obj,
    pub left_value: Obj,
    pub rewritten_right: Obj,
    pub right_value: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub aggregate_evaluations: Vec<AggregateEvaluationResult>,
    pub function_evaluations: Vec<FunctionApplicationEvaluationResult>,
    pub algo_evaluations: Vec<AlgoApplicationEvaluationResult>,
}

impl Runtime {
    // Exact closed aggregate computation, after the caller's whole equality WD.
    // Algorithm dispatch must cite its proved function equation before a term
    // can contribute mathematical equality evidence.
    pub fn search_equal_fact_by_aggregate_calculation(
        &mut self,
        fact: &EqualFact,
        _state: VerifyState,
    ) -> RuntimeResult<Option<AggregateCalculationBuiltinRuleProof>> {
        if !(contains_aggregate(&fact.left) || contains_aggregate(&fact.right)) {
            return Ok(None);
        }
        let (rewritten_left, mut cited_equal_fact_ids) =
            self.rewrite_obj_by_known_closed_numeric_equal(&fact.left);
        let (rewritten_right, right_cites) =
            self.rewrite_obj_by_known_closed_numeric_equal(&fact.right);
        cited_equal_fact_ids.extend(right_cites);
        let mut context = ActiveAlgoCalls::new();
        context.proof_mode = true;
        context.function_proof_state = _state;
        let left_value = match evaluate_obj(self, &rewritten_left, 0, &mut context)? {
            Ok(v) => v,
            Err(_) => return Ok(None),
        };
        let right_value = match evaluate_obj(self, &rewritten_right, 0, &mut context)? {
            Ok(v) => v,
            Err(_) => return Ok(None),
        };
        if !objs_equal_by_rational_expression_evaluation(&left_value, &right_value) {
            return Ok(None);
        }
        cited_equal_fact_ids.extend(context.cited_equal_fact_ids);
        Ok(Some(AggregateCalculationBuiltinRuleProof {
            rewritten_left,
            left_value,
            rewritten_right,
            right_value,
            cited_equal_fact_ids,
            aggregate_evaluations: context.aggregate_evaluations,
            function_evaluations: context.function_evaluations,
            algo_evaluations: context.algo_evaluations,
        }))
    }
}

fn contains_aggregate(obj: &Obj) -> bool {
    match obj {
        Obj::IteratedOperator(
            IteratedOperator::Sum(_)
            | IteratedOperator::Product(_)
            | IteratedOperator::SumOfFiniteSet(_)
            | IteratedOperator::ProductOfFiniteSet(_),
        ) => true,
        Obj::IteratedOperator(
            IteratedOperator::Reduce(_) | IteratedOperator::FiniteSetReduce(_),
        ) => true,
        Obj::ArithmeticOperator(op) => match op {
            ArithmeticOperator::Add(v) => {
                contains_aggregate(&v.left) || contains_aggregate(&v.right)
            }
            ArithmeticOperator::Sub(v) => {
                contains_aggregate(&v.left) || contains_aggregate(&v.right)
            }
            ArithmeticOperator::Mul(v) => {
                contains_aggregate(&v.left) || contains_aggregate(&v.right)
            }
            ArithmeticOperator::Div(v) => {
                contains_aggregate(&v.left) || contains_aggregate(&v.right)
            }
            ArithmeticOperator::Pow(v) => {
                contains_aggregate(&v.base) || contains_aggregate(&v.exponent)
            }
            ArithmeticOperator::Max(v) => {
                contains_aggregate(&v.left) || contains_aggregate(&v.right)
            }
            ArithmeticOperator::Min(v) => {
                contains_aggregate(&v.left) || contains_aggregate(&v.right)
            }
            ArithmeticOperator::Neg(v) => contains_aggregate(&v.arg),
            ArithmeticOperator::Abs(v) => contains_aggregate(&v.arg),
            ArithmeticOperator::Floor(v) => contains_aggregate(&v.arg),
            ArithmeticOperator::Ceil(v) => contains_aggregate(&v.arg),
            ArithmeticOperator::Sign(v) => contains_aggregate(&v.arg),
        },
        _ => false,
    }
}
