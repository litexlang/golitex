//! Statement execution results for new_pipeline.
//!
//! Contract:
//! - `exec_stmt` matches stmt kind and calls `exec_xxx_stmt`
//! - each `exec_xxx_stmt` returns a dedicated `ExecXxxStmtResult`
//! - fields sit flat on that result (no nested Effect / WellDefined wrappers):
//!   how it ran, env effect mirrors, optional closed local env

use crate::new_pipeline::ast::stmt::{DefPropStmt, LetObjStmt};
use crate::new_pipeline::execute::execute_fact_stmt::{
    ExecFactStmtResult, FactWellDefinedProof, ParamTypeWellDefinedProof, VerifyObjResult,
};
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

// Pipeline: WD the RHS value → affect global env. No local env.
pub struct ExecLetObjStmtResult {
    pub statement: LetObjStmt,
    pub value_well_defined: VerifyObjResult,
    pub stored_fact_ids: Vec<FactId>,
}

// Pipeline: open local → WD param types + iff-facts → close local → store prop.
pub struct ExecDefPropStmtResult {
    pub statement: DefPropStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub iff_fact_well_defined: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
    pub prop_name: String,
}
