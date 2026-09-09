// 用来存像 forall a R, exist a R 这种时候开个局部环境，做局部声名，产生的结果
pub struct LocalParameterDefinitionResult {
    pub symbols: Vec<String>,
    pub symbol_ids: Vec<SymbolId>,
    pub parameter_type_assumption_results: Vec<AssumptionResult>,
}

pub struct AssumptionResult {
    pub fact_id: FactId,
    pub well_defined_result: FactWellDefinedProof,
}
