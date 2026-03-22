use super::Runtime;
use crate::error::ExecStmtError;
use crate::error::StoreFactError;
use crate::fact::Fact;
use crate::infer::InferResult;
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    pub fn store_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: &Fact,
    ) -> Result<InferResult, StoreFactError> {
        self.runtime_context
            .top_level_env()
            .store_fact(fact.clone())?;

        self.runtime_context
            .top_level_env()
            .store_fact_to_cache_known_fact(fact)?;

        let infer_result = self
            .infer(fact)
            .map_err(|e| StoreFactError::new(format!("infer error: {}", e), Some(e.into())))?;
        Ok(infer_result)
    }

    pub fn verify_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, ExecStmtError> {
        self.verify_fact_well_defined(fact, verify_state)?;
        self.store_fact_without_well_defined_verified_and_infer(fact)
            .map_err(ExecStmtError::from)
    }
}
