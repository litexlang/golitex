use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::FailToVerifyObjWellDefinedResult;

pub struct FailToVerifyNotForallFactWellDefinedResult {
    pub reason: FailToVerifyObjWellDefinedResult,
}
