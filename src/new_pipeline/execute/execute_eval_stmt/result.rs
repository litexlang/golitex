//! Result types for `eval expr`.

use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::EvalStmt;
use crate::new_pipeline::runtime::runtime_ids::FactId;

pub enum ExecCommandStmtResult {
    Eval(ExecEvalStmtResult),
}

pub enum ExecEvalStmtResult {
    Success(ExecEvalStmtSuccess),
    Failed(ExecEvalStmtFailed),
}

// Success fields follow exec_eval_stmt stage order:
// statement → rewrite → evaluate.
pub struct ExecEvalStmtSuccess {
    pub statement: EvalStmt,
    pub source_object: Obj,
    pub rewritten_object: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub evaluated_object: Obj,
}

pub enum ExecEvalStmtFailed {
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
