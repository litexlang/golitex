//! Result types for `eval expr`.

use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::ast::stmt::EvalStmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::execute::execute_fact_stmt::{VerifyEqualFactWellDefinedResult, VerifyFactResult};
use crate::runtime::runtime_ids::FactId;
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub enum ExecCommandStmtResult {
    Eval(ExecEvalStmtResult),
}

pub enum ExecEvalStmtResult {
    Success(ExecEvalStmtSuccess),
    Failed(ExecEvalStmtFailed),
}

// Success fields follow exec_eval_stmt stage order:
// statement → source WD → rewrite → evaluate → checked algorithm equations
// → result equality WD → publish. The exact evaluator is the computation
// certificate; every algorithm application additionally cites its definition.
pub struct ExecEvalStmtSuccess {
    pub statement: EvalStmt,
    pub source_object: Obj,
    pub source_well_defined: ObjWellDefinedProof,
    pub rewritten_object: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub evaluated_object: Obj,
    pub aggregate_evaluations: Vec<super::aggregate_evaluation_result::AggregateEvaluationResult>,
    pub function_evaluations:
        Vec<super::aggregate_evaluation_result::FunctionApplicationEvaluationResult>,
    pub algo_evaluations: Vec<super::aggregate_evaluation_result::AlgoApplicationEvaluationResult>,
    pub evaluated_equal_fact: EqualFact,
    pub evaluated_equal_well_defined: EqualFactWellDefinedProof,
    pub store_and_infer_result: StoreFactAndInferResult,
}

pub enum ExecEvalStmtFailed {
    WellDefined(Box<VerifyObjWellDefinedResult>),
    AlgorithmEquation(Box<VerifyFactResult>),
    EvaluatedEqualityWellDefined(Box<VerifyEqualFactWellDefinedResult>),
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
