use crate::prelude::*;
use crate::verify_rewrite::VerifyState;

// Result of opening a local env and declaring parameters, e.g. forall a R / exist a R.
pub struct LocalParamsDefResults {
    pub symbols: Vec<String>,
    pub symbol_ids: Vec<SymbolId>,
    pub parameter_type_assumption_results: Vec<AssumptionResult>,
}

pub struct AssumptionResult {
    pub fact_id: FactId,
    pub well_defined_result: FactWellDefinedProof,
}

impl Runtime {
    // Used when proving forall, and when proving forall/exist well-definedness.
    pub fn local_params_define(
        &mut self,
        typed_parameters: TypedParameterList,
    ) -> Result<LocalParamsDefResults, RuntimeError> {
        let _ = typed_parameters;
        todo!("define local parameters")
    }

    // Local assume for domain facts, e.g. a > 0 in forall a R: a > 0 => $p(a).
    pub fn local_assume(
        &mut self,
        assumptions: Vec<Fact>,
    ) -> Result<Vec<AssumptionResult>, RuntimeError> {
        let _ = assumptions;
        todo!("assume local facts")
    }
}
