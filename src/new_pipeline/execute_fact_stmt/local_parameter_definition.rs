use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

// Result of opening a local env and declaring parameters, e.g. forall a R / exist a R.
pub struct LocalParamsDefResults2 {
    pub symbols: Vec<String>,
    pub symbol_ids: Vec<SymbolId>,
    pub parameter_type_assumption_results: Vec<AssumptionResult2>,
}

pub struct AssumptionResult2 {
    pub fact_id: FactId,
    pub well_defined_result: FactWellDefinedProof2,
}

impl Runtime {
    // Used when proving forall, and when proving forall/exist well-definedness.
    pub fn local_params_define2(
        &mut self,
        typed_parameters: TypedParameterList,
    ) -> Result<LocalParamsDefResults2, RuntimeError> {
        let _ = typed_parameters;
        todo!("define local parameters")
    }

    // Local assume for domain facts, e.g. a > 0 in forall a R: a > 0 => $p(a).
    pub fn local_assume2(
        &mut self,
        assumptions: Vec<Fact>,
    ) -> Result<Vec<AssumptionResult2>, RuntimeError> {
        let _ = assumptions;
        todo!("assume local facts")
    }
}
