use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyFactWellDefinedResult, FailToVerifyObjWellDefinedResult, FactWellDefinedProof,
};

pub enum FailToVerifyForallFactWellDefinedResult {
    ParamType(FailToVerifyObjWellDefinedResult),
    DomFact {
        failed_index: usize,
        succeeded_dom_well_defined: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
}
