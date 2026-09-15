//! Statement execution results for new_pipeline.
//!
//! Top level dispatches by stmt kind only. Soft Success|Failed lives inside
//! each leaf `*Result`. Session-stopping bugs stay in `RuntimeResult::Err`.

use crate::new_pipeline::execute::execute_def_abstract_prop_stmt::ExecDefAbstractPropStmtSuccessResult;
use crate::new_pipeline::execute::execute_def_prop_stmt::ExecDefPropStmtResult;
use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult;
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::ExecHaveObjInNonemptySetStmtResult;
use crate::new_pipeline::execute::execute_let_stmt::ExecLetObjStmtResult;
use crate::new_pipeline::execute::execute_unsafe_stmt::ExecUnsafeStmtResult;

pub enum ExecStmtResult {
    Fact(ExecFactStmtResult),
    Definition(ExecDefinitionStmtResult),
    Unsafe(ExecUnsafeStmtResult),
}

pub enum ExecDefinitionStmtResult {
    LetObj(ExecLetObjStmtResult),
    HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult),
    DefProp(ExecDefPropStmtResult),
    DefAbstractProp(ExecDefAbstractPropStmtSuccessResult),
}

impl ExecStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Fact(r) => r.is_failed(),
            Self::Definition(r) => r.is_failed(),
            Self::Unsafe(r) => r.is_failed(),
        }
    }
}

impl ExecDefinitionStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::LetObj(r) => r.is_failed(),
            Self::HaveObjInNonemptySet(r) => r.is_failed(),
            Self::DefProp(r) => r.is_failed(),
            Self::DefAbstractProp(_) => false,
        }
    }
}
