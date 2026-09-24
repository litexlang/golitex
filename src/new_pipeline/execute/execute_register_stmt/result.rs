use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyFactResult;

pub enum ExecRegisterStmtResult {
    ReflexiveProp(ExecRegisterReflexivePropStmtResult),
    SymmetricProp(ExecRegisterSymmetricPropStmtResult),
    TransitiveProp(ExecRegisterTransitivePropStmtResult),
}

impl ExecRegisterStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::ReflexiveProp(r) => r.is_failed(),
            Self::SymmetricProp(r) => r.is_failed(),
            Self::TransitiveProp(r) => r.is_failed(),
        }
    }
}

pub enum ExecRegisterReflexivePropStmtResult {
    Success(ExecRegisterReflexivePropStmtSuccess),
    Failed(ExecRegisterReflexivePropStmtFailed),
}

pub struct ExecRegisterReflexivePropStmtSuccess {
    pub prop: AtomicName,
    pub forall_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecRegisterReflexivePropStmtFailed {
    Shape(String),
    PropNotDefined(String),
    WrongArity {
        prop: AtomicName,
        expected: usize,
        actual: usize,
    },
    Forall(VerifyFactResult),
}

impl ExecRegisterReflexivePropStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecRegisterSymmetricPropStmtResult {
    Success(ExecRegisterSymmetricPropStmtSuccess),
    Failed(ExecRegisterSymmetricPropStmtFailed),
}

pub struct ExecRegisterSymmetricPropStmtSuccess {
    pub prop: AtomicName,
    pub forall_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecRegisterSymmetricPropStmtFailed {
    Shape(String),
    PropNotDefined(String),
    WrongArity {
        prop: AtomicName,
        expected: usize,
        actual: usize,
    },
    Forall(VerifyFactResult),
}

impl ExecRegisterSymmetricPropStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecRegisterTransitivePropStmtResult {
    Success(ExecRegisterTransitivePropStmtSuccess),
    Failed(ExecRegisterTransitivePropStmtFailed),
}

pub struct ExecRegisterTransitivePropStmtSuccess {
    pub prop: AtomicName,
    pub forall_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecRegisterTransitivePropStmtFailed {
    Shape(String),
    PropNotDefined(String),
    WrongArity {
        prop: AtomicName,
        expected: usize,
        actual: usize,
    },
    Forall(VerifyFactResult),
}

impl ExecRegisterTransitivePropStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
