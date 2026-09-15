//! Statement execution results for new_pipeline.
//!
//! Top level is always Success | Failed (soft miss). Session-stopping bugs stay
//! in `RuntimeResult::Err` (SessionError).
//!
//! Success / Failed each mirror stmt kind; definition / unsafe nest further.

use crate::new_pipeline::ast::stmt::{HaveObjInNonemptySetOrParamTypeStmt, LetObjStmt};
use crate::new_pipeline::execute::execute_def_abstract_prop_stmt::ExecDefAbstractPropStmtResult;
use crate::new_pipeline::execute::execute_def_prop_stmt::ExecDefPropStmtResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    ExecFactStmtResult, ParamTypeWellDefinedProof, VerifyFactResult, VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_unsafe_stmt::ExecUnsafeStmtResult;
use crate::new_pipeline::runtime::FactId;

pub enum ExecStmtResult {
    Success(ExecStmtSuccess),
    Failed(ExecStmtFailed),
}

pub enum ExecStmtSuccess {
    Fact(ExecFactStmtResult),
    Definition(ExecDefinitionStmtSuccess),
    Unsafe(ExecUnsafeStmtResult),
}

pub enum ExecStmtFailed {
    Fact(VerifyFactResult),
    Definition(ExecDefinitionStmtFailed),
    Unsafe(ExecUnsafeStmtFailed),
}

pub enum ExecDefinitionStmtSuccess {
    LetObj(ExecLetObjStmtResult),
    HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult),
    DefProp(ExecDefPropStmtResult),
    DefAbstractProp(ExecDefAbstractPropStmtResult),
}

pub enum ExecDefinitionStmtFailed {
    LetObj(VerifyObjWellDefinedResult),
    HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtFailed),
    DefProp(ExecDefPropStmtFailed),
}

pub enum ExecHaveObjInNonemptySetStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    NonemptyCheck(VerifyFactResult),
}

pub enum ExecDefPropStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    IffFactWellDefined(VerifyFactResult),
}

pub enum ExecUnsafeStmtFailed {
    Trust(VerifyFactResult),
    TrustHave(ExecTrustHaveStmtFailed),
}

pub enum ExecTrustHaveStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    BodyFactWellDefined(VerifyFactResult),
}

// Pipeline: WD the RHS value → affect global env. No local env.
pub struct ExecLetObjStmtResult {
    pub statement: LetObjStmt,
    pub value_well_defined: VerifyObjWellDefinedResult,
    pub stored_fact_ids: Vec<FactId>,
}

// Pipeline: WD param types → nonempty obligations → define symbols.
pub struct ExecHaveObjInNonemptySetStmtResult {
    pub statement: HaveObjInNonemptySetOrParamTypeStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub nonempty_checks: Vec<HaveObjGroupNonemptyCheckResult>,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
}

// One entry per TypedParameterGroup, mirroring ParamType.
pub enum HaveObjGroupNonemptyCheckResult {
    Set,
    NonemptySet,
    FiniteSet,
    Obj(VerifyFactResult),
}

pub struct StoreHaveObjAndInferResult {
    pub stored_fact_ids: Vec<FactId>,
}
