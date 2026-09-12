//! Statement execution results for new_pipeline.
//!
//! Contract:
//! - `exec_stmt` matches stmt kind and calls `exec_xxx_stmt`
//! - each `exec_xxx_stmt` returns a dedicated `ExecXxxStmtResult`
//! - result fields mirror that function's pipeline:
//!   1. how it ran (verify / well-defined track)
//!   2. how it affected the global ExecEnv (mirror only; ExecEnv is authoritative)
//!   3. Option: closed local ExecEnv if the pipeline opened one

use crate::new_pipeline::ast::stmt::{DefPropStmt, LetObjStmt};
use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult;
use crate::new_pipeline::execution_environment::exec_env::ExecEnv;
use crate::new_pipeline::runtime::FactId;

pub enum ExecStmtResult {
    Fact(ExecFactStmtResult),
    Definition(ExecDefinitionStmtResult),
}

pub enum ExecDefinitionStmtResult {
    LetObj(ExecLetObjStmtResult),
    DefProp(ExecDefPropStmtResult),
}

// Pipeline: well-defined gate → affect global env. No local env.
pub struct ExecLetObjStmtResult {
    pub statement: LetObjStmt,
    pub well_defined: LetObjWellDefinedResult,
    pub effect: LetObjEffect,
}

// Tracer WD: only numbers and `+` are accepted for now.
pub struct LetObjWellDefinedResult {}

pub struct LetObjEffect {
    pub stored_fact_ids: Vec<FactId>,
}

// Pipeline: open local env → well-defined in local → close local into result → affect global env.
pub struct ExecDefPropStmtResult {
    pub statement: DefPropStmt,
    pub well_defined: DefPropWellDefinedResult,
    pub local_env: Box<ExecEnv>,
    pub effect: DefPropEffect,
}

// Tracer WD: parameter/body checks are not fully wired yet; this marks the local phase ran.
pub struct DefPropWellDefinedResult {}

pub struct DefPropEffect {
    pub prop_name: String,
}
