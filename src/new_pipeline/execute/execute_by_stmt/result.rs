use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyFactResult;

pub enum ExecByStmtResult {
    PropRegistration(ExecByPropRegistrationStmtResult),
}

pub enum ExecByPropRegistrationStmtResult {
    Success(ExecByPropRegistrationStmtSuccess),
    Failed(ExecByPropRegistrationStmtFailed),
}

pub struct ExecByPropRegistrationStmtSuccess {
    pub prop: AtomicName,
    pub forall_proof: VerifyFactResult,
}

pub enum ExecByPropRegistrationStmtFailed {
    Shape(String),
    PropNotDefined(String),
    WrongArity {
        prop: AtomicName,
        expected: usize,
        actual: usize,
    },
    Forall(VerifyFactResult),
}

impl ExecByStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::PropRegistration(r) => r.is_failed(),
        }
    }
}

impl ExecByPropRegistrationStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
