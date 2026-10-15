use crate::prelude::*;

pub(in crate::json_output) fn project_eval_failure(
    failed: &crate::execute::ExecEvalStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::ExecEvalStmtFailed;
    use crate::json_output::failure_kind::FailureKind;
    use crate::json_output::helper::{object_for, string, with_failure_diagnostic};
    let (cause, kind) = match failed {
        ExecEvalStmtFailed::UnsupportedExpression => {
            ("unsupported_expression", FailureKind::Unsupported)
        }
        ExecEvalStmtFailed::EvaluationFailed => ("evaluation_failed", FailureKind::Evaluation),
        ExecEvalStmtFailed::AlgoDispatchFailed => {
            ("algo_dispatch_failed", FailureKind::AlgorithmDispatch)
        }
        ExecEvalStmtFailed::DepthExceeded => ("depth_exceeded", FailureKind::DepthLimit),
        ExecEvalStmtFailed::CyclicAlgoCall => ("cyclic_algo_call", FailureKind::CyclicEvaluation),
        ExecEvalStmtFailed::AggregateBudgetExceeded => {
            ("aggregate_budget_exceeded", FailureKind::AggregateBudget)
        }
        ExecEvalStmtFailed::AggregateRangeOverflow => {
            ("aggregate_range_overflow", FailureKind::AggregateRange)
        }
        ExecEvalStmtFailed::WellDefined(result) => {
            return super::wd::project_verify_obj_wd(result, runtime)
        }
        ExecEvalStmtFailed::AlgorithmEquation(result) => {
            return super::verify::project_verify_fact(result, runtime)
        }
        ExecEvalStmtFailed::EvaluatedEqualityWellDefined(result) => {
            return super::wd::project_verify_equal_wd(result, runtime)
        }
    };
    with_failure_diagnostic(
        runtime,
        object_for(runtime, vec![("cause", string(cause))]),
        kind,
        vec![],
    )
}
