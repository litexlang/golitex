//! Completed explicit-definition stages in an unaccepted detached scope.
use crate::prelude::*;

pub struct ExecByDefLocalFailure {
    pub statement: crate::ast::stmt::ByDefStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub failure: ExecByDefEnteredFailed,
    pub local_env: Box<ExecEnv>,
}

impl ExecByDefLocalFailure {
    pub fn new(
        statement: crate::ast::stmt::ByDefStmt,
        goal_wd: VerifyFactWellDefinedResult,
        failure: ExecByDefEnteredFailed,
        local_env: Box<ExecEnv>,
    ) -> Self {
        Self {
            statement,
            goal_wd,
            failure,
            local_env,
        }
    }
}

pub enum ExecByDefEnteredFailed {
    Definition(DefinitionProofFailed),
    Proof {
        definition: crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchProofByDefinition,
        result: VerifyFactResult,
    },
}

pub struct ExecByDefStoreFailure {
    pub statement: crate::ast::stmt::ByDefStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
    pub message: String,
}

impl ExecByDefStoreFailure {
    pub fn new(
        statement: crate::ast::stmt::ByDefStmt,
        goal_wd: VerifyFactWellDefinedResult,
        proof: VerifyFactResult,
        local_env: Box<ExecEnv>,
        message: String,
    ) -> Self {
        Self {
            statement,
            goal_wd,
            proof,
            local_env,
            message,
        }
    }
}
