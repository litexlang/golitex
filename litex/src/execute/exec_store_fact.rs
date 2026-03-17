use crate::error::ExecError;
use crate::verify::VerifyState;
use crate::fact::Fact;
use super::Executor;
use crate::error::StoreFactError;

impl<'a> Executor<'a> {
    pub fn store_fact_without_well_defined_verified_and_infer(&mut self, fact: &Fact) -> Result<(), StoreFactError> {
        self.runtime_context.top_level_env().store_fact(fact.clone())?;

        self.runtime_context.top_level_env().store_fact_to_cache_known_fact(fact)?;
        
        self.infer(fact).map_err(|e| StoreFactError::new(format!("infer error: {}", e), Some(e.into())))?;
        Ok(())
    }

    pub fn verify_fact_well_defined_and_store_and_infer(&mut self, fact: &Fact, verify_state: &VerifyState) -> Result<(), ExecError> {
        self.verify_fact_well_defined(fact, verify_state)?;
        self.store_fact_without_well_defined_verified_and_infer(fact)?;
        Ok(())
    }
}
