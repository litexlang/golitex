use super::aggregate_evaluation_result::{AlgoApplicationEvaluationResult, AlgoDefinitionEvidence};
use super::result::ExecEvalStmtFailed;
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::execute::execute_by_stmt::proof_verify_state;
use crate::runtime::{Runtime, RuntimeResult};

// Certify the equations used by concrete algorithm execution before publishing
// its final value. Check each finite trace step independently: a recursive
// algorithm may execute recursively, but this check never recursively evaluates
// an algorithm or enlarges the equality search's premise permissions.
pub(super) fn verify_evaluated_algo_calls(
    runtime: &mut Runtime,
    evaluations: &mut [AlgoApplicationEvaluationResult],
) -> RuntimeResult<Result<(), ExecEvalStmtFailed>> {
    for evaluation in evaluations {
        let Obj::FnObj(original_call) = &evaluation.application else {
            return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression));
        };
        let mut normalized_call = original_call.clone();
        let mut arguments = evaluation.normalized_arguments.iter();
        for group in &mut normalized_call.body {
            for argument in group {
                let Some(value) = arguments.next() else {
                    return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
                };
                *argument = Box::new(value.clone());
            }
        }
        if arguments.next().is_some() {
            return Ok(Err(ExecEvalStmtFailed::AlgoDispatchFailed));
        }
        // Argument normalization is supplied by the preceding exact evaluation
        // trace. The selected case's mathematical equation is checked at those
        // concrete arguments, including signature and branch conditions.
        let equal = EqualFact {
            fact_id: runtime.global_ids.allocate_fact_id(),
            left: Obj::FnObj(normalized_call),
            right: evaluation.return_expression.clone(),
            line_file: None,
        };
        let proof = runtime.verify_equal_fact(&equal, proof_verify_state())?;
        if proof.is_failed() {
            return Ok(Err(ExecEvalStmtFailed::AlgorithmEquation(Box::new(proof))));
        }
        evaluation.definition_evidence = AlgoDefinitionEvidence::Checked(proof);
    }
    Ok(Ok(()))
}
