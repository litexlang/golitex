//! Successful evaluation command outcomes.

use crate::prelude::*;

pub struct SuccessEvalStmtResult {
    pub statement: EvalStmt,
    pub common: SuccessStmtCommonResult,
    /// The execution layer selected for this `eval`. A configured trusted
    /// source can deliberately skip evaluation; verified execution owns the exact source
    /// and resulting object and, when available, the recursive numeric
    /// computation selected by the evaluator.
    pub execution: SuccessEvalStmtExecutionResult,
}

pub enum SuccessEvalStmtExecutionResult {
    SkippedByTrustedExecution,
    Evaluated(Box<SuccessEvaluatedEvalStmtResult>),
}

pub struct SuccessEvaluatedEvalStmtResult {
    pub source_object: Obj,
    pub evaluated_object: Obj,
    /// Closed numeric evaluation already has a complete recursive result.
    /// Other runtime algorithms remain explicit but fail closed in the
    /// standalone compiler until they gain their own typed computation tree.
    pub recursive_numeric_evaluation: Option<SuccessEvaluateObjResult>,
}

pub enum SuccessCommandStmtResult {
    EvalStmt(Box<SuccessEvalStmtResult>),
}
