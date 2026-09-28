//! Proposition, setting, and template definition outcomes.

use crate::prelude::*;

pub struct SuccessDefPropStmtResult {
    pub statement: DefPropStmt,
    pub common: SuccessStmtCommonResult,
    /// Verified concrete propositions are checked in a temporary environment
    /// containing their typed parameters. Trusted materialization deliberately
    /// retains no invented verification evidence.
    pub run_in_local_env: Option<SuccessVerifyDefPropLocalEnvResult>,
}

/// Typed output of checking one concrete proposition definition before its
/// parameter scope is popped. The body entries retain the exact recursive WD
/// trees needed to render function applications in proof-producing targets.
pub struct SuccessVerifyDefPropLocalEnvResult {
    pub binder: SuccessVerifyFactBinderResult,
    pub body: Vec<SuccessVerifyLocalFactWellDefinedResult>,
}

pub struct SuccessDefAbstractPropStmtResult {
    pub statement: DefAbstractPropStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessDefSettingStmtResult {
    pub statement: DefSettingStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessDefTemplateStmtResult {
    pub statement: DefTemplateStmt,
    pub template_parameter_groups: Vec<SuccessVerifyFactParameterGroupResult>,
    pub template_domain_results: Vec<SuccessVerifyLocalFactWellDefinedResult>,
    pub body_statement_result: Box<SuccessStmtResult>,
}
