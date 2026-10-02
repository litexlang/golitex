//! Result types for `eval expr`.

use crate::ast::obj::Obj;
use crate::ast::stmt::EvalStmt;
use crate::execute::execute_fact_stmt::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::runtime::runtime_ids::FactId;

pub enum ExecCommandStmtResult {
    Eval(ExecEvalStmtResult),
}

pub enum ExecEvalStmtResult {
    Success(ExecEvalStmtSuccess),
    Failed(ExecEvalStmtFailed),
}

// Success fields follow exec_eval_stmt stage order:
// statement → source WD → rewrite → evaluate.
pub struct ExecEvalStmtSuccess {
    pub statement: EvalStmt,
    pub source_object: Obj,
    pub source_well_defined: ObjWellDefinedProof,
    pub rewritten_object: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub evaluated_object: Obj,
    pub aggregate_evaluations: Vec<super::aggregate_evaluation_result::AggregateEvaluationResult>,
    pub function_evaluations: Vec<super::aggregate_evaluation_result::FunctionApplicationEvaluationResult>,
    pub algo_evaluations: Vec<super::aggregate_evaluation_result::AlgoApplicationEvaluationResult>,
}

pub enum ExecEvalStmtFailed {
    WellDefined(Box<VerifyObjWellDefinedResult>),
    // Residual shape is not a closed-numeric tree and not an algo call we can run.
    UnsupportedExpression,
    // Closed-numeric residual that still fails exact/decimal evaluation (e.g. /0).
    EvaluationFailed,
    // Identifier FnObj with no matching stored algo / bad arity / no matching case.
    AlgoDispatchFailed,
    // Recursion budget exhausted (nested algo / arithmetic depth).
    DepthExceeded,
    // Same algo call is already being evaluated on the active stack.
    CyclicAlgoCall,
    AggregateBudgetExceeded,
    AggregateRangeOverflow,
}

impl ExecCommandStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Eval(r) => r.is_failed(),
        }
    }
}

impl ExecEvalStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
