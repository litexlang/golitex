//! Structure definition and field-check outcomes.

use crate::prelude::*;
use std::rc::Rc;

pub struct SuccessDefStructStmtResult {
    pub statement: DefStructStmt,
    pub common: SuccessStmtCommonResult,
    /// The definition is checked in a temporary environment containing only
    /// its structure parameters and fields. Trusted materialization retains
    /// the definition but deliberately carries no invented verification.
    pub run_in_local_env: Option<SuccessVerifyDefStructLocalEnvResult>,
}

/// Typed output of `def_struct_stmt_check_well_defined_result` before its local
/// environment is popped. This is not a `StmtResult`: the local operation is
/// the verification process for the enclosing `def struct`, not another
/// source statement.
pub struct SuccessVerifyDefStructLocalEnvResult {
    /// Output of defining the structure parameters from the definition. These are
    /// structure parameters, not template parameters.
    pub structure_parameter_definition: Option<SuccessInferResult>,
    pub structure_domains: Vec<SuccessVerifyDefStructDomainResult>,
    pub field_types: Vec<SuccessVerifyDefStructFieldTypeResult>,
    pub field_scope_run_in_local_env: SuccessVerifyDefStructFieldScopeResult,
}

pub struct SuccessVerifyDefStructDomainResult {
    pub domain_index: usize,
    pub proposition: Fact,
    pub well_definedness: WellDefinedFactResult,
}

pub struct SuccessVerifyDefStructFieldTypeResult {
    pub field_index: usize,
    pub binding: SymbolBinding,
    pub field_type: Obj,
    pub well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
}

/// Typed output of the nested field environment. Field definitions and
/// equivalent facts are ordinary semantic operations owned by the enclosing
/// definition, so neither is wrapped in a synthetic statement Result.
pub struct SuccessVerifyDefStructFieldScopeResult {
    pub field_definitions: Vec<SuccessVerifyDefStructFieldDefinitionResult>,
    pub equivalent_facts: Vec<SuccessVerifyLocalFactWellDefinedResult>,
}

pub struct SuccessVerifyDefStructFieldDefinitionResult {
    pub field_index: usize,
    pub binding: SymbolBinding,
    pub field_type: Obj,
    pub infers: SuccessInferResult,
}
