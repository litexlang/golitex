//! Statement execution results for new_pipeline.
//!
//! Contract:
//! - `exec_stmt` matches stmt kind and calls `exec_xxx_stmt`
//! - each `exec_xxx_stmt` returns a dedicated `ExecXxxStmtResult`
//! - fields sit flat on that result (no nested Effect / WellDefined wrappers):
//!   how it ran, env effect mirrors, optional closed local env

use crate::new_pipeline::ast::stmt::{HaveObjInNonemptySetOrParamTypeStmt, LetObjStmt};
use crate::new_pipeline::execute::execute_def_abstract_prop_stmt::ExecDefAbstractPropStmtResult;
use crate::new_pipeline::execute::execute_def_prop_stmt::ExecDefPropStmtResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    ExecFactStmtResult, ParamTypeWellDefinedProof, VerifyFactResult, VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_unsafe_stmt::ExecUnsafeStmtResult;
use crate::new_pipeline::runtime::FactId;

pub enum ExecStmtResult {
    Fact(ExecFactStmtResult),
    Definition(ExecDefinitionStmtResult),
    Unsafe(ExecUnsafeStmtResult),
}

pub enum ExecDefinitionStmtResult {
    LetObj(ExecLetObjStmtResult),
    HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult),
    DefProp(ExecDefPropStmtResult),
    DefAbstractProp(ExecDefAbstractPropStmtResult),
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
