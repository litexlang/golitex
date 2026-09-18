//! Statement execution results for new_pipeline.
//!
//! Top level dispatches by stmt kind only. Soft Success|Failed lives inside
//! each leaf `*Result`. Session-stopping bugs stay in `RuntimeResult::Err`.
//!
//! Shared ParamType-indexed shells live here so `have` / `witness` / later
//! args:type checks reuse one shape.

use crate::new_pipeline::execute::execute_by_stmt::ExecByStmtResult;
use crate::new_pipeline::execute::execute_def_abstract_prop_stmt::ExecDefAbstractPropStmtSuccessResult;
use crate::new_pipeline::execute::execute_def_prop_stmt::ExecDefPropStmtResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    ExecFactStmtResult, VerifyFactResult, VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::ExecHaveObjInNonemptySetStmtResult;
use crate::new_pipeline::execute::execute_let_stmt::ExecLetObjStmtResult;
use crate::new_pipeline::execute::execute_unsafe_stmt::ExecUnsafeStmtResult;
use crate::new_pipeline::execute::execute_witness_stmt::ExecWitnessStmtResult;

// WD of one parameter-type annotation (not a Fact).
// Example: `x R` → Obj(WD of `R`); bare `set` → Set.
pub enum ParamTypeWellDefinedProof {
    Set,
    NonemptySet,
    FiniteSet,
    Obj(VerifyObjWellDefinedResult),
}

// Fact obligation indexed by ParamType.
// Example: `have x S` nonempty check; `witness … from w` with `w $in S`.
pub enum ParamTypeFactCheckResult {
    Set,
    NonemptySet,
    FiniteSet,
    Obj(VerifyFactResult),
}

impl ParamTypeWellDefinedProof {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Obj(wd) => wd.is_failed(),
            Self::Set | Self::NonemptySet | Self::FiniteSet => false,
        }
    }
}

impl ParamTypeFactCheckResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::Obj(r) => r.is_failed(),
            Self::Set | Self::NonemptySet | Self::FiniteSet => false,
        }
    }
}

pub enum ExecStmtResult {
    Fact(ExecFactStmtResult),
    Definition(ExecDefinitionStmtResult),
    Witness(ExecWitnessStmtResult),
    Unsafe(ExecUnsafeStmtResult),
    By(ExecByStmtResult),
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
            Self::Witness(r) => r.is_failed(),
            Self::Unsafe(r) => r.is_failed(),
            Self::By(r) => r.is_failed(),
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
