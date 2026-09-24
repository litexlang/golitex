//! Result types for `have algo for fn …`.

use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::ast::obj::{FnSet, Obj};
use crate::new_pipeline::ast::param::TypedParameterList;
use crate::new_pipeline::ast::stmt::DefAlgoStmt;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyFactResult;

pub enum ExecDefAlgoStmtResult {
    Success(ExecDefAlgoStmtSuccess),
    Failed(ExecDefAlgoStmtFailed),
}

// Success fields follow exec_def_algo_stmt stage order.
pub struct ExecDefAlgoStmtSuccess {
    pub statement: DefAlgoStmt,
    pub setup: ExecDefAlgoSetup,
    pub cases: Vec<ExecDefAlgoCaseAgreement>,
    pub closing: ExecDefAlgoClosing,
}

pub struct ExecDefAlgoSetup {
    pub fn_set: FnSet,
    pub parameter_definition: TypedParameterList,
    pub function_call: Obj,
    pub requirement_facts: Vec<Fact>,
}

pub struct ExecDefAlgoCaseAgreement {
    pub case_index: usize,
    pub verification_fact: Fact,
    pub verification: VerifyFactResult,
}

pub enum ExecDefAlgoClosing {
    Default(ExecDefAlgoBranchAgreement),
    Coverage(ExecDefAlgoCoverageAgreement),
}

pub struct ExecDefAlgoBranchAgreement {
    pub verification_fact: Fact,
    pub verification: VerifyFactResult,
}

pub struct ExecDefAlgoCoverageAgreement {
    pub verification_fact: Fact,
    pub verification: VerifyFactResult,
}

pub enum ExecDefAlgoStmtFailed {
    TargetFnMissing,
    AlgoAlreadyDefined,
    BadShape(String),
    Case {
        case_index: usize,
        verification_fact: Fact,
        verification: VerifyFactResult,
    },
    Default {
        verification_fact: Fact,
        verification: VerifyFactResult,
    },
    Coverage {
        verification_fact: Fact,
        verification: VerifyFactResult,
    },
}

impl std::fmt::Debug for ExecDefAlgoStmtFailed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TargetFnMissing => write!(f, "TargetFnMissing"),
            Self::AlgoAlreadyDefined => write!(f, "AlgoAlreadyDefined"),
            Self::BadShape(msg) => write!(f, "BadShape({msg})"),
            Self::Case { case_index, .. } => write!(f, "Case(index={case_index})"),
            Self::Default { .. } => write!(f, "Default"),
            Self::Coverage { .. } => write!(f, "Coverage"),
        }
    }
}

impl ExecDefAlgoStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
