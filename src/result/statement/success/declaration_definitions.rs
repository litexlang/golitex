//! Algorithm, theorem, axiom, and strategy definition outcomes.

use crate::prelude::*;

/// Canonical successful statement result. Its shape mirrors `Stmt` recursively;
/// statement-specific evidence is owned only by the matching leaf variant.
pub struct SuccessDefAlgoStmtResult {
    pub statement: DefAlgoStmt,
    pub common: SuccessStmtCommonResult,
    pub run_in_local_env: Option<SuccessVerifyDefAlgoLocalEnvResult>,
}

pub struct SuccessVerifyDefAlgoLocalEnvResult {
    pub definition_function_set: FnSetBody,
    pub parameter_retagging: Vec<SuccessVerifyDefAlgoParameterRetagResult>,
    pub requirement_facts: Vec<Fact>,
    pub parameter_definition: TypedParameterList,
    pub function_call: Obj,
    pub cases: Vec<SuccessVerifyDefAlgoCaseResult>,
    pub default_return: Option<SuccessVerifyDefAlgoDefaultResult>,
    pub coverage: Option<SuccessVerifyDefAlgoCoverageResult>,
}

pub struct SuccessVerifyDefAlgoParameterRetagResult {
    pub parameter_index: usize,
    pub source_binding: SymbolBinding,
    pub verification_object: Obj,
}

pub struct SuccessVerifyDefAlgoCaseResult {
    pub case_index: usize,
    pub verification_fact: Fact,
    pub verification: Box<StmtResult>,
}

pub struct SuccessVerifyDefAlgoDefaultResult {
    pub verification_fact: Fact,
    pub verification: Box<StmtResult>,
}

pub struct SuccessVerifyDefAlgoCoverageResult {
    pub verification_fact: Fact,
    pub verification: Box<StmtResult>,
}

pub struct SuccessDefThmStmtResult {
    pub statement: DefThmStmt,
    pub common: SuccessStmtCommonResult,
    pub source_fact_id: FactId,
    pub verification: Option<SuccessVerifyTheoremResult>,
}

pub struct SuccessAxiomStmtResult {
    pub statement: AxiomStmt,
    pub common: SuccessStmtCommonResult,
    pub well_definedness: Option<SuccessVerifyFactWellDefinedResult>,
}

pub struct SuccessDefStrategyStmtResult {
    pub statement: DefStrategyStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyStrategyDefinitionResult>,
}
