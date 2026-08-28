//! Structured proof-failure output attached to runtime errors.

use crate::prelude::*;

#[derive(Debug)]
pub struct RuntimeErrorOutput {
    pub failed_step: Option<Box<Stmt>>,
    pub failed_goal: Option<Box<Fact>>,
    pub proof_step_index: Option<usize>,
    pub proof_step_count: Option<usize>,
    pub then_clause_index: Option<usize>,
    pub then_clause_count: Option<usize>,
    pub unknown_result: Option<RuntimeErrorUnknownResult>,
}

#[derive(Debug)]
pub enum RuntimeErrorUnknownResult {
    Generic(UnknownGenericStmtResult),
    Fact(Box<UnknownFactResult>),
}

impl RuntimeErrorOutput {
    pub fn new() -> Self {
        RuntimeErrorOutput {
            failed_step: None,
            failed_goal: None,
            proof_step_index: None,
            proof_step_count: None,
            then_clause_index: None,
            then_clause_count: None,
            unknown_result: None,
        }
    }

    pub fn proof_step_unknown(
        failed_step: Stmt,
        proof_step_index: usize,
        proof_step_count: usize,
        result: &StmtResult,
    ) -> Self {
        let mut output = Self::new();
        output.failed_step = Some(Box::new(failed_step));
        output.proof_step_index = Some(proof_step_index);
        output.proof_step_count = Some(proof_step_count);
        output.unknown_result = RuntimeErrorUnknownResult::from_stmt_result(result);
        output
    }

    pub fn then_clause_unknown(
        failed_goal: Fact,
        then_clause_index: usize,
        then_clause_count: usize,
        result: &StmtResult,
    ) -> Self {
        let mut output = Self::new();
        output.failed_goal = Some(Box::new(failed_goal));
        output.then_clause_index = Some(then_clause_index);
        output.then_clause_count = Some(then_clause_count);
        output.unknown_result = RuntimeErrorUnknownResult::from_stmt_result(result);
        output
    }

    pub fn goal_unknown(failed_goal: Fact, result: &StmtResult) -> Self {
        let mut output = Self::new();
        output.failed_goal = Some(Box::new(failed_goal));
        output.unknown_result = RuntimeErrorUnknownResult::from_stmt_result(result);
        output
    }
}

impl RuntimeErrorUnknownResult {
    pub fn from_stmt_result(result: &StmtResult) -> Option<Self> {
        if let Some(unknown) = result.as_fact_unknown() {
            return Some(RuntimeErrorUnknownResult::Fact(Box::new(unknown.clone())));
        }
        result.as_unknown().map(|unknown| {
            RuntimeErrorUnknownResult::Generic(UnknownGenericStmtResult {
                detail: unknown.detail.clone(),
            })
        })
    }
}
